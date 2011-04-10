;;; server-maze.el --- server for maze clients

;; Copyright (C) 2011  SAKURAI Masashi

;; Author: SAKURAI Masashi <m.sakurai at kiwanami.net>
;; Keywords: games

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; TODO
;; メインのスレッド化
;; 移動まとめる

;; ■プロトコル

;; S:Server, Ca:Target Client, Cn:All Clients

;; ○接続時
;; Ca > S | (name string:name)
;; S > Ca | (map int:width int:height string:maptext int:id float:init-x float:init-y float:angle) ; マップ生成
;; S > Ca | (move list:(int:id string:name float:x float:y float:angle)) ; 移動通知でみんなのデータもらう。ここで更新
;; 
;; ○接続通知
;; S > Cn | (connect int:id string:name float:x float:y float:angle)
;;
;; ○移動時
;; Ca > S | (move float:x float:y float:angle)
;; 
;; ○移動通知
;; S > Cn | (move list:(int:id string:name float:x float:y float:angle))
;; 
;; ○切断通知
;; S > Cn | (disconnect int:id string:name)



;;; Code:

(require 'cl)
(require 'derived)
(require 'concurrent)
(require 'matrix)

(defstruct ssm:map width height maptext map objects)
(defstruct ssm:client id name x y angle)

(defvar ssm:scale 10.0 "MAP上の1文字のサイズ。壁の高さ。")
(defvar ssm:server-process-name "server-maze")
(defvar ssm:server-port 8765)
(defvar ssm:server-address nil "ホストのアドレス")

;; 現在保持している地図
(defvar ssm:map nil)

;; クライアント一覧 (list (process . client)...)
(defvar ssm:client-processes nil)

;; signal-channel ここに送るとクライアント全員にメッセージを送る
(defvar ssm:message-server nil)



;;==================================================
;; Utilities

(defvar ssm:debug-out t)
(defvar ssm:debug-buffer "*ssm log*")

(defun ssm:log-init ()
  (when (get-buffer ssm:debug-buffer)
    (kill-buffer ssm:debug-buffer)))

(defun ssm:log (&rest args)
  (when ssm:debug-out
    (with-current-buffer
        (get-buffer-create ssm:debug-buffer)
      (buffer-disable-undo)
      (goto-char (point-max))
      (insert (apply 'format args) "\n"))))

(defun ssm:define-keymap (keymap-list)
  (let ((map (make-sparse-keymap)))
    (mapc 
     (lambda (i)
       (define-key map
         (if (stringp (car i))
             (read-kbd-macro (car i)) (car i))
         (cdr i)))
     keymap-list)
    map))


;;==================================================
;; Map utilities

(defun ssm:build-map (src)
  (let* ((lines (split-string src "\n"))
         (width (loop for i in lines maximize (length i)))
         (height (length lines))
         (ret (make-vector (* width height) 1)))
    (loop for line in lines
          for j from 0 below (length lines)
          do 
          (loop for c across line
                for s = (char-to-string c)
                for i from 0 below (length line)
                for idx = (+ i (* width j))
                do
                (aset ret idx 
                      (if (or (eql c ?#) (eql c ?*)) 1 0))))
    (make-ssm:map :width width :height height 
                  :maptext 
                  (loop for i across ret
                        concat (if (< 0 i) "#" " "))
                  :map ret)))

(defun ssm:search-blank-pos (map)
  (mt:sxv 
   ssm:scale
   (mt:v+v (mt:vnew [0.5 0.5])
           (loop with w = (ssm:map-width map)
                 with h = (ssm:map-height map)
                 for i from 0 to 1000 
                 for x = (random w) for y = (random h)
                 for idx = (+ x (* y w))
                 do
                 (when (= 0 (aref (ssm:map-map map) idx))
                   (return (mt:vnew (vector x y))))
                 finally return (mt:vnew (vector 1 1))))))

(defun ssm:search-open-angle (map posv)
  (let* ((pos (mt:vfloor (mt:sxv (/ 1.0 ssm:scale) posv)))
         (x0 (mt:vref pos 0)) (y0 (mt:vref pos 1))
         (array (ssm:map-map map))
         (w (ssm:map-width map)))
    (labels
        ((check (x y)
                (let ((idx (+ x (* y w))))
                  (and (< idx (length array))
                       (= 0 (aref array idx))))))
      (cond
       ((check (1+ x0) y0) 0)
       ((check (1- x0) y0) 180)
       ((check x0 (1+ y0)) 90)
       ((check x0 (1- y0)) 270)
       (t 90)))))

;; (ssm:search-open-angle ssm:map (mt:vnew (vector 35 15)))


;;==================================================
;; Client process

(defvar ssm:uid 1)

(defun ssm:uid ()
  (incf ssm:uid))

(defun ssm:client-get-by-process (proc)
  (loop for (pp . client) in ssm:client-processes
        if (eq pp proc) 
        do (return client)
        finally return nil))

(defun ssm:client-get-by-id (id)
  (loop for (pp . client) in ssm:client-processes
        if (eq id (ssm:client-id client))
        do (return client)
        finally return nil))

(defun ssm:process-get-by-id (id)
  (loop for (pp . client) in ssm:client-processes
        if (eq id (ssm:client-id client))
        do (return pp)
        finally return nil))

(defun ssm:make-msg-init (map client)
  (format "%S\n" 
          (list 'map 
                (ssm:map-width map)
                (ssm:map-height map)
                (ssm:map-maptext map)
                (ssm:client-id client)
                (ssm:client-x client)
                (ssm:client-y client)
                (ssm:client-angle client))))

(defun ssm:make-msg-move (clients)
  (format 
   "%S\n"
   (list 'move
         (loop for i in clients
               collect
               (list (ssm:client-id i)
                     (ssm:client-name i)
                     (ssm:client-x i)
                     (ssm:client-y i)
                     (ssm:client-angle i))))))

(defun ssm:make-msg-connect (client)
  (format "%S\n" (list 'connect 
                     (ssm:client-id client) 
                     (ssm:client-name client)
                     (ssm:client-x client)
                     (ssm:client-y client)
                     (ssm:client-angle client))))

(defun ssm:make-msg-disconnect (client)
  (format "%S\n" (list 'disconnect 
                     (ssm:client-id client) 
                     (ssm:client-name client))))

(defun ssm:client-connect (message proc)
  (ssm:log "++ CONNECT [%s]  %S" message proc)
  (let* ((content (read message))
         (name (cadr content))
         (posv (ssm:search-blank-pos ssm:map))
         (client (make-ssm:client 
                  :id (ssm:uid)
                  :name name
                  :x (mt:vref posv 0)
                  :y (mt:vref posv 1)
                  :angle (ssm:search-open-angle ssm:map posv))))
    (ssm:log "   [%S]" client)
    (process-send-string 
     proc (ssm:make-msg-init ssm:map client))
    (process-send-string 
     proc (ssm:make-msg-move (mapcar 'cdr ssm:client-processes)))
    (cc:signal-send ssm:message-server
                    'ssm:all (ssm:make-msg-connect client))
    (setq ssm:client-processes
          (cons (cons proc client)
                ssm:client-processes))))

(defun ssm:client-move (proc client message)
  (ssm:log "<< RECEIVE  %s : %s" (ssm:client-name client) line)
  (let* ((content (read message))
         (x (nth 1 content))
         (y (nth 2 content))
         (a (nth 3 content)))
    (setf (ssm:client-x client)     x)
    (setf (ssm:client-y client)     y)
    (setf (ssm:client-angle client) a)
    (cc:signal-send
     ssm:message-server
     'ssm:all (ssm:make-msg-move (list client)))))

(defun ssm:client-disconnect (client)
  (ssm:log "DISCONNECT %s" (ssm:client-name client))
  (cc:signal-send
   ssm:message-server
   'ssm:all (ssm:make-msg-disconnect client)))

(defun ssm:client-ban (client)
  (ssm:log "BAN %s" (ssm:client-name client))
  (ssm:client-abort (ssm:process-get-by-id (ssm:client-id client))))

(defun ssm:client-abort (process)
  (ssm:log "ABORT %S" process)
  (when process
    (delete-process process)))


;;==================================================
;; Server 

(defun ssm:client-listener (process message)
  (let ((client (ssm:client-get-by-process process))
        (line (substring message 0 -1)))
    (cond
     ((null client)
      (condition-case err
          (ssm:client-connect line process)
        ('error 
         (ssm:log "Protocol error: %S" err)
         (ssm:client-abort process))))
     (t
      (condition-case err
          (ssm:client-move process client line)
        ('error 
         (ssm:log "Protocol error: %S" err)))))))

(defun ssm:client-sentinel (process msg)
  (setq ssm:client-processes
        (loop for (proc . client) in ssm:client-processes
              unless (eq process proc)
              collect (cons proc client)
              else
              do 
              (ssm:client-disconnect client))))

(defun ssm:client-send-message (args)
  (destructuring-bind (event (message)) args
    (cond
     ((eq 'ssm:all event)
      (loop for (prc . client) in ssm:client-processes
            do
            (process-send-string prc (concat message "\n"))
            (ssm:log ">> SENT %s" (ssm:client-name client))))
     (t
      (ssm:log "!! Not supported message type: %s / %S" event message)))))

(defun ssm:server-start () 
  (interactive)
  (ssm:log-init)
  (let ((maze-buf (find-file-noselect "maze.txt")))
    (setq ssm:map 
          (ssm:build-map 
           (with-current-buffer maze-buf
             (buffer-string)))))
  (setq ssm:client-processes nil)
  (setq ssm:message-server (cc:signal-channel 'ssm:server))
  (cc:signal-connect ssm:message-server
                     'ssm:all 'ssm:client-send-message)
  (make-network-process 
   :name ssm:server-process-name
   :buffer "*message-server*"
   :family 'ipv4 :server t
   :host ssm:server-address :service ssm:server-port
   :sentinel 'ssm:client-sentinel
   :filter 'ssm:client-listener)
  (ssm:log "SERVER START")
  (ssm:open-management-buffer))

(defun ssm:server-stop ()
  (interactive)
  (loop for (proc . client) in ssm:client-processes
        do (delete-process proc)
        (ssm:log "DELETE CLIENT : %s" (ssm:client-name client)))
  (setq ssm:client-processes nil)
  (delete-process ssm:server-process-name)
  (ssm:log "SERVER STOP"))


;;==================================================
;; Management buffer

;; run で動作中 stop で停止指示 nil で停止中
(defvar ssm:management-thread nil)
(defvar ssm:management-thread-on-finish nil)

(defun ssm:management-thread-start ()
  (when (null ssm:management-thread)
    (setq ssm:management-thread 'run)
    (ssm:log ">> Management Thread Start:")
    (cc:thread 
     1000
     (while (eq ssm:management-thread 'run)
       (with-current-buffer
           (get-buffer ssm:management-buffer)
         (ssm:management-update-buffer)))
     (progn
       (ssm:log "<< Management Thread Stop:")
       (setq ssm:management-thread nil)
       (funcall ssm:management-thread-on-finish))))) ; 停止処理

(defun ssm:management-thread-stop (on-finish-task)
  (cond
   ((eq ssm:management-thread 'run)
    (setq ssm:management-thread-on-finish on-finish-task)
    (setq ssm:management-thread 'stop))
   (t (funcall on-finish-task))))

(defvar ssm:management-mode-map 
  (ssm:define-keymap
   '(
     ("g"       . ssm:management-update-buffer)
     ("b"       . ssm:management-ban-client)
     ("q"       . ssm:management-quit)
     )))

(define-derived-mode ssm:management-mode
  fundamental-mode 
  "Maze Management mode"
  "Maze Management mode"
  )

(defvar ssm:management-buffer "*maze server management*")

;; サーバー構築後に呼ばれる
(defun ssm:open-management-buffer ()
  (let ((buf (get-buffer-create ssm:management-buffer)))
    (with-current-buffer buf
      (ssm:management-mode)
      (buffer-disable-undo)
      (setq buffer-read-only t)
      (ssm:management-update-buffer))
    (switch-to-buffer buf)
    (ssm:management-thread-start)))

(defface ssm:face-title 
  '((((class color) (background light))
     :foreground "MediumBlue" :height 1.5 :inherit variable-pitch)
    (((class color) (background dark))
     :foreground "yellow" :weight bold :height 1.5 :inherit variable-pitch)
    (t :height 1.5 :weight bold :inherit variable-pitch))
  "" :group 'ssm)

(defface ssm:face-subtitle
  '((((class color))
     :foreground "Gray10" :height 1.2 :inherit variable-pitch)
    (t :height 1.2 :inherit variable-pitch))
  "" :group 'ssm)

(defface ssm:face-item
  '((t :inherit variable-pitch :foreground "DarkSlateBlue"))
  "" :group 'ssm)

(defface ssm:face-mark-client
  '((t :foreground "DarkOliveGreen" :background "Darkseagreen1"))
  "" :group 'ssm)

(defface ssm:face-mark-floor
  '((t :foreground "white" :background "Rosybrown2"))
  "" :group 'ssm)

(defface ssm:face-mark-wall
  '((t :foreground "LightBlue" :background "MediumBlue"))
  "" :group 'ssm)

(defun ssm:rt (text face)
  (unless (stringp text) (setq text (format "%s" text)))
  (put-text-property 0 (length text) 'face face text) text)

(defun ssm:rt-format (text &rest args)
  (apply 'format (ssm:rt text 'ssm:face-item)
         (loop for i in args
               if (consp i)
               collect (ssm:rt (car i) (cdr i))
               else
               collect (ssm:rt i 'ssm:face-subtitle))))

(defun ssm:management-ip-address ()
  (mapconcat 'identity
             (loop for (name . addr) in (network-interface-list)
                   unless (equal name "lo")
                   collect (format-network-address addr t))
             ", "))

;; 内容を更新する
(defun ssm:management-update-buffer ()
  (interactive)
  (save-excursion
    (let (buffer-read-only (EOL "\n"))
      (erase-buffer)
      (insert (ssm:rt "Maze Server Management:" 'ssm:face-title) EOL EOL)
      (insert (ssm:rt-format
               "IP Address: %s  Port: %s"
               (ssm:management-ip-address) 
               ssm:server-port) EOL EOL)
      (insert (ssm:management-layout-map) EOL EOL)
      (insert (ssm:rt "Client List:" 'ssm:face-subtitle) EOL)
      (insert (format "%03s  %6s   (position) angle" 'id 'name) EOL)
      (insert 
       (or
        (loop for (p . c) in ssm:client-processes 
              concat
              (format "%03d  %6s   (%2.3f  %2.3f)  %3.1f\n"
                      (ssm:client-id c) (ssm:client-name c)
                      (ssm:client-x c) (ssm:client-y c) (ssm:client-angle c)))
        "No clients")))))

(defun ssm:management-layout-map ()
  (let* ((width  (ssm:map-width ssm:map))
         (height (ssm:map-height ssm:map))
         (org  (ssm:map-map ssm:map))
         (WALL (ssm:rt (substring "#" 0) 'ssm:face-mark-wall))
         (FLR  (ssm:rt (substring " " 0) 'ssm:face-mark-floor))
         (scr (make-vector (* width height) FLR)))
    (loop for y from 0 below height do
          (loop for x from 0 below width
                for idx = (+ x (* y width))
                if (= (aref org idx) 1)
                do (aset scr idx WALL)))
    (loop for (p . c) in ssm:client-processes 
          for x = (floor (/ (ssm:client-x c) ssm:scale))
          for y = (floor (/ (ssm:client-y c) ssm:scale))
          for idx = (+ x (* y width))
          if (and (<= 0 idx) (< idx (length org)))
          do 
          (aset scr idx 
                (ssm:rt
                 (substring-no-properties 
                  (format "%s" (ssm:client-name c))
                  0 1) 'ssm:face-mark-client)))
    (mapconcat 'identity
               (loop for y from 0 below height 
                     collect
                     (loop for x from 0 below width
                           for idx = (+ x (* y width))
                           concat (aref scr idx)))
               "\n")))

(defun ssm:management-quit ()
  (interactive)
  (when (y-or-n-p "Disconnect all clients and shutdown server ?")
    (lexical-let ((buf (current-buffer)))
      (ssm:management-thread-stop
       (lambda ()
         (ssm:server-stop)
         (kill-buffer buf)
         (ssm:log "<< Finish task: ok."))))))

(defun ssm:management-ban-client (id)
  (interactive "Mclient id:")
  (let ((client (ssm:client-get-by-id (string-to-number id))))
    (if client
        (progn
          (when (y-or-n-p (format "Do you ban the client [%s]?" (ssm:client-name client)))
            (ssm:client-ban client)
            (message "Client [%s] banned." (ssm:client-name client))))
      (message "Client [%s] not found." id))))

;; (global-set-key (kbd "M-0") 'ssm:server-start)

;; (eval-current-buffer)
;; (ssm:server-start)
;; (ssm:server-stop)
;; (list-processes)
;; (setq ssm:server-address "127.0.0.1")

;; (setq ssm:debug-out nil)
;; (setq ssm:debug-out t)

(provide 'server-maze)

