;;; client-maze.el --- maze clients

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

;; ICON表示
;;   ICON取得、キャッシュ
;;   表示（文字の上に表示？）
;; 一覧表示
;; 地図に表示

;; See 3dmaze.el for details.


;;; Code:

(require 'cl)
(require 'derived)
(require 'concurrent)
(require 'widget)
(require 'wid-edit)
(require 'matrix)

(defstruct csm:map width height map objects)
(defstruct csm:buf width height tbuf zbuf)
(defstruct csm:object id name def pos angle)

;; 全体の見え方に対するパラメーター
(defvar csm:scale 10.0 "MAP上の1文字のサイズ。壁の高さ。")
(defvar csm:aperture-size 30.0 "描画すべき画角。単位degree。")

;; csm:map-tbuf に入れるオブジェクトのタイプ
(defconst csm:tbuf-none    00)
(defconst csm:tbuf-air     01)
(defconst csm:tbuf-floor   02)
(defconst csm:tbuf-floor2  03)
(defconst csm:tbuf-wall    04)
(defconst csm:tbuf-out     08)
(defconst csm:tbuf-other   16)
(defconst csm:tbuf-other-side   17)
(defconst csm:tbuf-other-back   18)
(defconst csm:tbuf-me      64)

(defconst csm:zbuf-inf    1e10 "Zバッファの無限遠")
(defvar   csm:zbuf-fogout  80.0 "fogで完全に消えてしまう距離（csm:zlimitよりも遠い方が良い）")
(defvar   csm:zlimit       60.0 "スキャン打ち切り距離")

(defconst csm:chr  ?\  "bufferに実際にinsertする文字")

(defvar csm:debug-out nil)
(defvar csm:debug-buffer "*maze log*")

(defun csm:log-init ()
  (when (get-buffer csm:debug-buffer)
    (kill-buffer csm:debug-buffer)))

(defun csm:log (&rest args)
  (when csm:debug-out
    (with-current-buffer
        (get-buffer-create csm:debug-buffer)
      (buffer-disable-undo)
      (goto-char (point-max))
      (insert (apply 'format args) "\n"))))

(defun csm:define-keymap (keymap-list)
  (let ((map (make-sparse-keymap)))
    (mapc 
     (lambda (i)
       (define-key map
         (if (stringp (car i))
             (read-kbd-macro (car i)) (car i))
         (cdr i)))
     keymap-list)
    map))

(defun csm:world-new (map screen pos angle)
  (list map screen pos angle))

(defsubst csm:world-map (world)
  (car world))

(defsubst csm:world-screen (world)
  (cadr world))

(defsubst csm:world-pos (world)
  (nth 2 world))

(defsubst csm:world-set-pos (world pos)
  (setf (nth 2 world) pos))

(defsubst csm:world-angle (world)
  (nth 3 world))

(defsubst csm:world-set-angle (world angle)
  (setf (nth 3 world) angle))

(defsubst csm:d2r (deg)
  (/ (* pi deg) 180.0))

(defsubst csm:d2f (deg)
  (/ (* 1024 deg) 360))

(defsubst csm:f2d (deg)
  (/ (* 360.0 deg) csm:table-num))

(defsubst csm:degree (d)
  (setq d (floor d))
  (cond
   ((< d 0) (+ d 360))
   ((>= d 360) (- d 360))
   (t d)))

(defsubst csm:degreef (d)
  (setq d (floor d))
  (cond
   ((< d 0) (+ d csm:table-num))
   ((>= d csm:table-num) (- d csm:table-num))
   (t d)))

;; 固定小数点演算を仮定
;; 値を1024倍して保持しておく
;; 固定小数点の変数は -f をつける
;; 30bit整数まで扱えるので、掛け算1回ぐらいならオーバーフローしないはず

(defvar csm:fx 1024.0 "固定小数基数")
(defvar csm:fxi 1024 "固定小数基数")

(defsubst csm:tofx (v)
  (floor (* v csm:fx)))

(defsubst csm:fromfx (v)
  (/ v csm:fx))

(defsubst csm:tofxv (v)
  (mt:vfloor2d (mt:sxv2d csm:fx v)))

(defsubst csm:fromfxv (v)
  (mt:sxv2d (/ 1.0 csm:fx) v))

;; 角度について
;; - 入出力：0-360
;; - テーブル参照： csm:table-num 


(defvar csm:table-num 1024 "三角関数テーブルの要素数。1度1つで360個。")

(defun csm:table-init (func)
  (loop for i from 0 below csm:table-num
        with array = (make-vector csm:table-num 0)
        do (aset array i 
                 (csm:tofx 
                  (min 1048576 ;1024*1024
                       (funcall func (csm:d2r (/ (* 360.0 i) csm:table-num))))))
        finally return array))

(defvar csm:table-sin (csm:table-init 'sin) "三角関数テーブル sin")
(defvar csm:table-cos (csm:table-init 'cos) "三角関数テーブル cos")
(defvar csm:table-tan (csm:table-init 'tan) "三角関数テーブル tab")

(defsubst csm:sin-f (degree)
  (aref csm:table-sin degree))

(defsubst csm:cos-f (degree)
  (aref csm:table-cos degree))

(defsubst csm:tan-f (degree)
  (aref csm:table-tan degree))

(defun csm:init-table-scanz ()
  (vconcat 
   (loop with zf = (csm:tofx 1)
         until (> zf (csm:tofx csm:zlimit))
         collect
         (let ((ret zf))
           (cond
            ((< zf (/ (csm:tofx csm:scale) 2))
             (incf zf (/ (csm:tofx csm:scan-scale) 4)))
            ((< zf (csm:tofx csm:scale))
             (incf zf (/ (csm:tofx csm:scan-scale) 3)))
            ((< zf (csm:tofx (* 2 csm:scale)))
             (incf zf (csm:tofx csm:scan-scale)))
            (t 
             (incf zf (csm:tofx (* 2 csm:scan-scale)))))
           ret))))

(defvar csm:scan-scale 1.6 "動径方向のスキャンサイズ単位")
(defvar csm:table-scanz (csm:init-table-scanz)
  "Zスキャンの距離配列。近くはきめ細かく、遠くは荒くを表現。")
;;(length csm:table-scanz)


(defvar csm:table-wall-num  80
  "距離→壁の高さを変換するテーブル（個数）")
(defvar csm:table-wall-delta-f nil
  "距離→壁の高さを変換するテーブルの変換単位 ( zf / delta -> index )
 FIXME: should be buffer local")
(defvar csm:table-wall nil "距離→壁の高さを変換するテーブル。
スクリーン高さに依存するのでバッファ初期化時に決まる。
 FIXME: should be buffer local")

(defun csm:init-table-wall (window-height)
  (setq csm:table-wall-delta-f (csm:tofx (/ csm:zlimit csm:table-wall-num)))
  (setq csm:table-wall
        (loop for i from 0 below csm:table-wall-num
              with delta = (/ csm:zlimit csm:table-wall-num)
              with ret = (make-vector csm:table-wall-num 0)
              for z = (* delta (max i 1))
              do (aset ret i (round (* (/ csm:scale z) window-height 0.8)))
              finally return ret)))

(defsubst csm:wall-f (zf)
  (let ((idx (/ zf csm:table-wall-delta-f)))
    (cond
     ((< idx 0) (setq idx 0))
     ((>= idx csm:table-wall-num)
      (setq idx (1- csm:table-wall-num))))
    (aref csm:table-wall idx)))


;;==================================================
;; 接続情報入力

(defvar csm:dialog-buffer-name "*maze dialog*")
(defvar csm:dialog-value-name   nil)
(defvar csm:dialog-value-server nil)
(defvar csm:dialog-value-port   nil)
(defvar csm:dialog-window-num   nil)

(defun csm:dialog-startup ()
  (let (buf)
    (setq csm:dialog-window-num (length (window-list)))
    (when (get-buffer csm:dialog-buffer-name)
      (kill-buffer csm:dialog-buffer-name))
    (setq buf (get-buffer-create csm:dialog-buffer-name))
    (with-current-buffer buf
      (buffer-disable-undo)
      (widget-insert "Maze Client: Connect to\n\n")
      (lexical-let (fname fserver fport)
        (setq fname (widget-create
                     'editable-field
                     :size 20 :format   "  Name:           %v \n"
                     :value (or csm:dialog-value-name user-real-login-name ""))
              fserver (widget-create
                       'editable-field
                       :size 20 :format "  Server Address: %v \n"
                       :value (or csm:dialog-value-server ""))
              fport (widget-create
                     'editable-field
                     :size 10 :format   "  Server Port:    %v \n"
                     :value (or csm:dialog-value-port "")))
        ;; OK / Cancel
        (widget-insert "\n")
        (widget-create 
         'push-button
         :notify (lambda (&rest ignore)
                   (setq csm:dialog-value-name (widget-value fname))
                   (setq csm:dialog-value-server (widget-value fserver))
                   (setq csm:dialog-value-port (widget-value fport))
                   (if (and (< 0 (length csm:dialog-value-name))
                            (< 0 (length csm:dialog-value-server))
                            (< 0 (length csm:dialog-value-port)))
                       (csm:dialog-on-ok)
                     (message "The fields should not be null!")))
         "Ok")
        (widget-insert " ")
        (widget-create
         'push-button
         :notify (lambda (&rest ignore)
                   (csm:dialog-kill-buffer))
         "Cancel")
        (widget-insert "\n")
        (use-local-map widget-keymap)
        (widget-setup)
        (goto-char (point-min))
        (widget-forward 1))
      (pop-to-buffer buf))))

(defun csm:dialog-kill-buffer ()
  (let ((win-num (length (window-list))))
    (when (and (not (one-window-p))
               (> win-num csm:dialog-window-num))
      (delete-window))
    (kill-buffer csm:dialog-buffer-name)))

(defun csm:dialog-on-ok ()
  (csm:dialog-kill-buffer)
  (csm:connect-server csm:dialog-value-name
                      csm:dialog-value-server 
                      csm:dialog-value-port))


;;==================================================
;; Server 通信関係

(defvar csm:connection-process nil "TCP接続オブジェクト") ; should be buffer local
(defvar csm:connection-map nil "現在稼働中のマップデータなど") ; should be buffer local
(defvar csm:connection-myid nil "自分のID") ; should be buffer local
(defvar csm:server-info (cc:dataflow-environment) "サーバーからもらう情報")
(defvar csm:filter-buffer nil "未処理データ")

(defun csm:connect-server (name server-address server-port)
  (csm:log ">> Connection start: %s / %s : %s" name server-address server-port)
  (when csm:connection-process
    (delete-process csm:connection-process))
  (cc:dataflow-clear csm:server-info 'map)
  (setq csm:connection-process
        (open-network-stream "maze connection" "*maze connection*" 
                             server-address (string-to-number server-port)))
  (setq csm:filter-buffer (get-buffer-create "*maze buffer*"))
  (with-current-buffer csm:filter-buffer
    (erase-buffer) (buffer-disable-undo))
  (set-process-filter csm:connection-process 'csm:client-process-filter)
  (set-process-sentinel csm:connection-process 'csm:client-process-sentinel)
  (process-send-string csm:connection-process (format "%S\n" (list 'name name)))
  (deferred:$
    (cc:dataflow-get csm:server-info 'map)
    (deferred:nextc it
      (lambda (data) 
        (destructuring-bind (map pos angle) data
          (csm:open-buffer map pos angle))))))

(defun csm:client-process-filter (process message)
  (csm:log "INCOMING: [%S]" message)
  (let (content)
    (with-current-buffer csm:filter-buffer
      (when message
        (goto-char (point-max))
        (insert message))
      (goto-char (point-min))
      (let ((pos (condition-case err
                     (scan-lists (point-min) 1 0)
                   ('scan-error (message "%S" err) nil))))
        (when pos
          (setq content (car (read-from-string (buffer-substring (point-min) pos))))
          (delete-region (point-min) pos))))
    (when content
      (csm:log "MGS: [%S]" content)
      (condition-case err
          (let* ((tag (car content)))
            (cond
             ((eq tag 'map)
              (csm:build-map-from-server content))
             ((eq tag 'move)
              (csm:notify-move content csm:connection-map))
             ((eq tag 'connect)
              (csm:notify-connect content csm:connection-map))
             ((eq tag 'disconnect)
              (csm:notify-disconnect content csm:connection-map))
             (t 
              (csm:log "!!Unknown Protocol Message : %s" tag)))
            (deferred:call 'csm:client-process-filter process nil))
        ('error (message "MsgError: %S / <= %S" err content))))))

(defun csm:client-process-sentinel (process msg)
  "切断された場合など"
  (csm:log "!! Process Sentinel : %S : %S" process msg)
  (if (y-or-n-p "Disconnected. Try to re-connect ?")
      (csm:connect-server csm:dialog-value-name
                          csm:dialog-value-server 
                          csm:dialog-value-port)
    (csm:command-quit)))

(defun csm:build-map-from-server (data)
  (destructuring-bind
      (tag width height src id ix iy angle) data
    (let* ((mapdata 
            (loop with ret = (make-vector (length src) 0)
                  for i from 0 below (length src)
                  for d across src
                  do (aset ret i (if (= (aref src i) ?#) 1 0))
                  finally return ret))
           (map (make-csm:map
                 :width width :height height
                 :map mapdata)))
      (setq csm:connection-myid id) ; fix me
      (setq csm:connection-map map) ; fix me
      (cc:dataflow-set csm:server-info 'map 
                       (list map (mt:vnew (vector ix iy)) angle))
      map)))

(defun csm:other-get-by-id (id map)
  (if (eq id csm:connection-myid) nil ; fix me
    (loop for i in (csm:map-objects map)
          if (eq id (csm:object-id i))
          do (return i)
          finally return nil)))
  
(defun csm:other-add (obj map)
  (push obj (csm:map-objects map)))

(defun csm:notify-move (data map)
  (let ((moves (cadr data)))
    (loop for (id name x y angle) in moves
          for obj = (csm:other-get-by-id id map)
          if obj do
          (setf (csm:object-pos obj) (mt:vnew (vector x y)))
          (setf (csm:object-angle obj) angle)
          else do
          (unless (eq id csm:connection-myid) ; fix me
            (csm:other-add 
             (make-csm:object :id id :name name :def (csm:object-def-get name)
                              :pos (mt:vnew (vector x y)) :angle angle) map))))
  (csm:post-event-task 'csm:explorer-update))

(defun csm:notify-connect (data map)
  (destructuring-bind (tag id name x y angle) data
    (message "Joined: %s" name)
    (csm:post-event-task 'csm:explorer-update)))

(defun csm:notify-disconnect (data map)
  (destructuring-bind (tag id name) data
    (setf (csm:map-objects map)
          (remove-if (lambda (i) (eq id (csm:object-id i))) 
                     (csm:map-objects map)))
    (csm:post-event-task 'csm:explorer-update)
    (message "Disconnected: %s" name)))

(defun csm:server-send-move (posv angle)
  (process-send-string 
   csm:connection-process
   (format "%S\n" (list 'move (mt:vref posv 0) (mt:vref posv 1) angle))))

(defun csm:server-disconnect ()
  (when csm:connection-process
    (set-process-sentinel csm:connection-process nil)
    (delete-process csm:connection-process)
    (setq csm:connection-process nil)
    (setq csm:connection-map nil)))


;;==================================================
;; メイン 画面表示

(defvar csm:buffer-main "*3d maze*")

(defun csm:open-buffer (map init-posv init-angle &optional screen-width screen-height)
  (let ((buf (get-buffer-create csm:buffer-main))
        (scr (csm:init-screen screen-width screen-height))
        world)
    (setq world (csm:world-new map scr (csm:tofxv init-posv) init-angle))
    (with-current-buffer buf
      (csm:init-table-wall (csm:buf-height scr))
      (csm:explorer-mode)
      (buffer-disable-undo)
      (setq d3m-world world)
      (csm:draw-world world)
      (csm:init-buffer buf world)
      (csm:update-buffer buf world))
    (switch-to-buffer buf)))

(defun csm:init-screen (&optional screen-width screen-height)
  "裏画面バッファの準備"
  (let* ((ww (or screen-width (window-width)))
         (wh (or screen-height (window-height))))
    (make-csm:buf :width ww :height wh
                  :tbuf (make-vector (* ww wh) csm:tbuf-none)
                  :zbuf (make-vector (* ww wh) (csm:tofx csm:zbuf-inf)))))

(defun csm:draw-world (world)
  (csm:clear-screen (csm:world-screen world))
  (csm:draw-wall world)
  (csm:draw-objects world)
  )
  

(defun csm:clear-screen (scr)
  (fillarray (csm:buf-tbuf scr) csm:tbuf-none)
  (fillarray (csm:buf-zbuf scr) (csm:tofx csm:zbuf-inf)))

(defun csm:draw-wall (world)
  (let* ((scr (csm:world-screen world)) (map (csm:world-map world))
         (tbuf (csm:buf-tbuf scr)) (zbuf (csm:buf-zbuf scr))
         (ww (csm:buf-width scr)) (wh (csm:buf-height scr)) wwe
         (hww (/ ww 2)) (hwh (/ wh 2))
         (angle-f (csm:tofx (csm:d2f (csm:world-angle world))))
         (pos-f (csm:world-pos world))
         (posxf (mt:vref pos-f 0)) (posyf (mt:vref pos-f 1))
         (dt-f (/ (csm:tofx (csm:d2f csm:aperture-size)) hww))
         (zlimit-f (csm:tofx csm:zlimit))
         (start-f (csm:tofx 1.0)) obj (rn-f (mt:vcp pos-f)))
    (setq wwe (- ww 1)) ; for loop step
    (loop for i from 0 below wwe by 2
          for px = (- i hww)
          for th = (csm:degreef (csm:fromfx (+ angle-f (* dt-f px))))
          for cosf = (csm:cos-f th) for sinf = (csm:sin-f th)
          do
          ;;(csm:log ">>> Scan way th: %04f  cosf: %S sinf: %S" th cosf sinf)
          (loop for zf across csm:table-scanz
                do
                (mt:vset2d rn-f 
                           (+ posxf (/ (* zf cosf) csm:fxi))
                           (+ posyf (/ (* zf sinf) csm:fxi)))
                (setq obj (csm:draw-wall-find-object map rn-f))
                ;;(csm:log "Scan ?: %s  d: %04f rn: %S" obj zf rn-f)
                (cond
                 ((eq obj csm:tbuf-wall)
                  (csm:draw-wall-draw-wall i zf)
                  (csm:draw-wall-draw-wall (1+ i) zf)
                  (return))
                 ((eq obj csm:tbuf-out)
                  (csm:draw-wall-draw-out i zf)
                  (csm:draw-wall-draw-out (1+ i) zf)
                  (return))
                 (t 
                  (csm:draw-wall-draw-floor i zf obj)
                  (csm:draw-wall-draw-floor (1+ i) zf obj)))))))

(defun csm:draw-wall-find-object (map v-f)
  (let* ((x (floor (csm:fromfx (/ (mt:vref v-f 0) csm:scale))))
         (y (floor (csm:fromfx (/ (mt:vref v-f 1) csm:scale)))))
    (cond
     ((or (< x 0) (< y 0)
          (>= x (csm:map-width map))
          (>= y (csm:map-height map)))
      csm:tbuf-out)
     (t 
      (let* ((idx (+ x (* y (csm:map-width map)))))
        (cond
         ((= 0 (aref (csm:map-map map) idx))
          (if (< 0 (logand (+ x y) 1))
              csm:tbuf-floor csm:tbuf-floor2))
         (t csm:tbuf-wall)))))))

(defun csm:draw-wall-draw-wall (x z-f)
  (let* ((wall (csm:wall-f z-f))
         (hwall (ceiling (/ wall 2.0)))
         (top (max 0 (- hwh hwall)))
         (btm (min (1- wh) (+ hwh hwall))))
    ;;(csm:log "# x: %2s  z: %06f" x z-f)
    (loop for i from top to btm
          for idx = (+ x (* i ww))
          do
          (aset tbuf idx csm:tbuf-wall)
          (aset zbuf idx z-f))))

(defun csm:draw-wall-draw-out (x z-f)
  ;; DO NOTHING
  )

(defun csm:draw-wall-draw-floor (x z-f obj)
  (let* ((wall (csm:wall-f z-f))
         (hwall (/ wall 2))
         (btm (min wh (+ hwall hwh))))
    ;;(csm:log "F x: %2s  z: %06f" x z-f)
    (loop for i from btm below wh
          for idx = (+ x (* i ww))
          for floorz = (aref zbuf idx)
          do
          (when (< z-f floorz)
            (aset tbuf idx obj)
            (aset zbuf idx z-f)))))

(defun csm:draw-objects (world)
  (loop for obj in (csm:map-objects 
                    (csm:world-map world)) 
        do
        (csm:draw-objects-one world obj)))

(defvar csm:letter-def-table (make-hash-table :test 'equal)
  "文字 -> mapのハッシュ")

(defun csm:object-def-get (chr)
  (let ((map (gethash chr csm:letter-def-table)))
    (unless map
      (setq map (csm:init-letter chr))
      (puthash chr map csm:letter-def-table))
    map))

(defvar csm:program-banner 
  (cond
   ((eq 'darwin system-type) "/usr/bin/banner")
   ((eq 'gnu/linux system-type) "/usr/bin/printerbanner")
   (t "banner"))
  "文字プログラム")

(defun csm:init-letter (letter)
  (let* ((src 
          (with-temp-buffer
            (call-process csm:program-banner nil t nil
                          "-w" "60" (format "%s" letter))
            (buffer-string)))
         (lines (split-string src "\n"))
         (height (loop for i in lines maximize (length i)))
         (width  (* 4 (length lines)))
         (ret (make-vector (* width height) 0)))
    (loop for line in lines
          for x from 0 below (length lines)
          do 
          (loop for c across line
                for y from 0 below (length line)
                for val = (if (eql c ?#) 1 0)
                for idx = (+ (* x 4) (* (- height y 1) width))
                do
                (aset ret idx        val)
                (aset ret (incf idx) val)
                (aset ret (incf idx) val)
                (aset ret (incf idx) val)))
    (make-csm:map :width width :height height :map ret)))

(defun csm:object-debug-out (object)
  (csm:log-init)
  (with-current-buffer (get-buffer-create csm:debug-buffer)
    (loop for y from 0 below (csm:map-height object) do
          (loop for x from 0 below (csm:map-width object) do
                (insert (if (= 1 (aref (csm:map-map object) 
                                       (+ x (* y (csm:map-width object)))))
                            "#" " ")))
          (insert "\n")))
  (pop-to-buffer csm:debug-buffer))
;; (csm:object-debug-out (csm:init-letter "@"))

(defun csm:draw-objects-one (world object)
  (let*
      ((scr (csm:world-screen world)) (map (csm:world-map world))
       (tbuf (csm:buf-tbuf scr)) (zbuf (csm:buf-zbuf scr))
       (ww (csm:buf-width scr)) (wh (csm:buf-height scr))
       (hww (/ ww 2)) (hwh (/ wh 2))
       (angle (csm:world-angle world))
       (posv (mt:sxv2d (/ 1.0 csm:fx) (csm:world-pos world)))
       (tposv (csm:object-pos object))
       (relv (mt:v-v2d tposv posv))
       (rad (atan (mt:vref relv 1) (mt:vref relv 0)))
       (degree (csm:degree (- angle (* 180 (/ rad pi)))))
       (vlen (mt:vlen2d relv))
       (aplimit (* 1.6 csm:aperture-size))
       (dw (/ wh csm:aperture-size)) cx)
    (cond
     ((and (<= 0 degree) (< degree aplimit))
      (setq cx (floor (- hww (* dw degree)))))
     ((and (< (- 360 aplimit) degree) (< degree 360))
      (setq cx (floor (+ hww (* dw (- 360 degree)))))))
    (when (or (< vlen 3.0) (> vlen csm:zlimit)) (setq cx nil))
    ;;(message "deg: %s  dist: %2.3f  cx: %s" degree vlen cx)
    (when cx
      (let* ((def (csm:object-def object))
             (trad (csm:d2r (csm:object-angle object)))
             (ip (mt:vip (mt:vunit relv)
                         (mt:vnew (vector (cos trad) (sin trad)))))
             (lw (csm:map-width def))
             (lh (csm:map-height def))
             (lmap (csm:map-map def))
             (hlw (/ lw 2)) (hlh (/ lh 2))
             (delta (* (/ csm:scale vlen) (/ csm:scale hlh))) ; 文字サイズ調整（適当）
             (vlenf (csm:tofx vlen))
             (type 
              (cond
               ((< ip -0.7071) ; (cos (/ pi 4))
                csm:tbuf-other)
               ((< ip 0.7071) ; (cos (/ (* 3 pi) 4))
                csm:tbuf-other-side)
               (t csm:tbuf-other-back))))
        (csm:log "OBJ: ip:%s  z-f:%S" ip vlenf)
        (loop for ly from 0 below lh
              for scry = (floor (+ (* 1.2 hwh) (* delta (- ly hlh)))) do
              (loop for lx from 0 below lw 
                    for scrx = (floor (+ cx (* delta (- lx hlw))))
                    for scridx = (+ scrx (* ww scry))
                    for sczf = (if (and (<= 0 scrx) (< scrx ww) (<= 0 scry) (< scry wh))
                                   (aref zbuf scridx))
                    for val = (aref lmap (+ lx (* ly lw))) do
                    (when (and sczf (= 1 val) (< vlenf sczf))
                      (aset tbuf scridx type)
                      (aset zbuf scridx vlenf))))))))


;;==================================================

(defvar csm:2dmap-display t "display switch 2D map")
(defvar csm:2dmap-radial  3.0  "map size")
(defvar csm:2dmap-rect-left   0.7 "left-top (0.0-1.0)")
(defvar csm:2dmap-rect-top    0.0 "left-top (0.0-1.0)")
(defvar csm:2dmap-rect-width  0.3 "width  (0.0-1.0)")
(defvar csm:2dmap-rect-height 0.3 "height (0.0-1.0)")

(defun csm:draw-2dmap (world)
  (when csm:2dmap-display
    (let*
        ((scr (csm:world-screen world)) (map (csm:world-map world))
         (lmap (csm:map-map map))
         (mapw (csm:map-width map)) (maph (csm:map-height map))
         (tbuf (csm:buf-tbuf scr)) (zbuf (csm:buf-zbuf scr))
         (ww (csm:buf-width scr)) (wh (csm:buf-height scr))
         (angle (csm:world-angle world))
         (posv (mt:sxv2d (/ 1.0 csm:fx) (csm:world-pos world)))
         (scrx (floor (* ww csm:2dmap-rect-left)))
         (scry (floor (* wh csm:2dmap-rect-top)))
         (scrw (floor (* ww csm:2dmap-rect-width))) (scrwe (1- scrw)) ; for loop step 
         (scrh (floor (* wh csm:2dmap-rect-height)))
         (scrhw (/ scrw 2)) (scrhh (/ scrh 2))
         (scrxe (+ scrx scrw)) (scrye (+ scry scrh))
         (rot (mt:mrot2d (csm:d2r (+ angle 90))))
         )
      ;;(csm:log "=====================")
      (loop for scryi from 0 below scrh
            for scryii = (- scryi scrhh)
            with basev0 = (mt:vnew [0 0])
            do
            (loop for scrxi from 0 below scrwe by 2
                  for scrxii = (- scrxi scrhw)
                  for basev = (mt:vset2d 
                               basev0
                               (* csm:2dmap-radial scrxii) 
                               (* 2 csm:2dmap-radial scryii))
                  for mapv = (mt:v+v2d= (mt:mxv2d rot basev) posv)
                  for mapx = (floor (/ (mt:vref mapv 0) csm:scale))
                  for mapy = (floor (/ (mt:vref mapv 1) csm:scale))
                  for idx = 
                  (if (and (<= 0 mapx) (< mapx mapw)
                           (<= 0 mapy) (< mapy maph))
                      (+ mapx (* mapy mapw)) nil)
                  for val = (if idx (aref lmap idx) nil)
                  for scridx = (+ scrxi scrx (* ww (+ scry scryi)))
                  for vlenz = (csm:tofx (mt:vlen2d basev))
                  do 
                  ;;(csm:log "mapx:%s  mapy:%s  idx:%s  val:%s" mapx mapy idx val)
                  (cond
                   ((and (= 0 scrxii) (= 0 scryii))
                    (aset tbuf scridx csm:tbuf-me)
                    (aset zbuf scridx vlenz)
                    (aset tbuf (1+ scridx) csm:tbuf-me)
                    (aset zbuf (1+ scridx) vlenz))
                   ((null val) 
                    (aset tbuf scridx csm:tbuf-out)
                    (aset zbuf scridx vlenz)
                    (aset tbuf (1+ scridx) csm:tbuf-out)
                    (aset zbuf (1+ scridx) vlenz))
                   ((= 1 val)
                    (aset tbuf scridx csm:tbuf-wall)
                    (aset zbuf scridx vlenz)
                    (aset tbuf (1+ scridx) csm:tbuf-wall)
                    (aset zbuf (1+ scridx) vlenz))
                   (t
                    (aset tbuf scridx csm:tbuf-floor)
                    (aset zbuf scridx vlenz)
                    (aset tbuf (1+ scridx) csm:tbuf-floor)
                    (aset zbuf (1+ scridx) vlenz))))))))


;;==================================================

(defun csm:init-buffer (buf world)
  "バッファに文字列を書き込み"
  (erase-buffer)
  (let* ((buffer-read-only nil)
         (scr (csm:world-screen world))
         (ww (csm:buf-width scr))
         (wh (csm:buf-height scr))
         (line (make-string ww csm:chr)))
    (loop for i from 0 below wh do
          (insert line "\n"))
    (goto-char (point-min))
    (csm:screen-bitblt buf world)))

(defstruct csm:color-set num delta array)

(defun csm:color-set-generate (base fog num)
  (let ((delta (/ csm:zbuf-fogout num)) cl)
    (make-csm:color-set
     :num num
     :delta (csm:tofx delta)
     :array
     (vconcat
      (loop for i from 0 below num
            for d = (* delta i)
            for param = (/ (- csm:zbuf-fogout d) csm:zbuf-fogout)
            for cl =
            (cond
             ((< csm:zbuf-fogout d) fog)
             ((< d 1.0) base)
             (t
              (mt:v+v 
               (mt:sxv param base)
               (mt:sxv (- 1.0 param) fog))))
            collect
            (list ':background
                  (format "#%02x%02x%02x" 
                          (mt:vref cl 0)
                          (mt:vref cl 1) 
                          (mt:vref cl 2))))))))

(defvar csm:color-set-floor
  (csm:color-set-generate (mt:vnew [130  71  51]) (mt:vnew [255 255 255]) 32))
(defvar csm:color-set-floor2 
  (csm:color-set-generate (mt:vnew [ 70  31  30]) (mt:vnew [255 255 255]) 32))
(defvar csm:color-set-wall 
  (csm:color-set-generate (mt:vnew [ 51  51 204]) (mt:vnew [255 255 255]) 32))

(defvar csm:color-set-other
  (csm:color-set-generate (mt:vnew [255  90  90]) (mt:vnew [255 255 255]) 32))
(defvar csm:color-set-other-side
  (csm:color-set-generate (mt:vnew [230 230  80]) (mt:vnew [255 255 255]) 32))
(defvar csm:color-set-other-back
  (csm:color-set-generate (mt:vnew [ 50  255 50]) (mt:vnew [255 255 255]) 32))

(defvar csm:color-default '(:background "white"))
(defvar csm:color-out     '(:background "lightgray"))
(defvar csm:color-me      '(:background "pink"))

(defun csm:color-set-get (set z-f)
  (let* ((idx (/ z-f (csm:color-set-delta set)))
         (array (csm:color-set-array set))
         (len (csm:color-set-num set)))
    (cond
     ((< idx 0) (aref array 0))
     ((< idx len) (aref array idx))
     (t (aref array (- len 2))))))

(defun csm:screen-color (type z-f)
  (cond
   ((eq type csm:tbuf-floor)  (csm:color-set-get csm:color-set-floor  z-f))
   ((eq type csm:tbuf-floor2) (csm:color-set-get csm:color-set-floor2 z-f))
   ((eq type csm:tbuf-wall)   (csm:color-set-get csm:color-set-wall   z-f))
   ((eq type csm:tbuf-other)  (csm:color-set-get csm:color-set-other  z-f))
   ((eq type csm:tbuf-other-side) (csm:color-set-get csm:color-set-other-side z-f))
   ((eq type csm:tbuf-other-back) (csm:color-set-get csm:color-set-other-back z-f))
   ((eq type csm:tbuf-me)     csm:color-me)
   ((eq type csm:tbuf-out)    csm:color-out)
   ((eq type csm:tbuf-none)   csm:color-default)
   (t  csm:color-default)))

(defun csm:screen-bitblt (buf world)
  "裏画面からバッファのテキストプロパティを書き換え"
  (let* ((buffer-read-only nil)
         (map (csm:world-map world))
         (scr (csm:world-screen world))
         (tbuf (csm:buf-tbuf scr))
         (zbuf (csm:buf-zbuf scr))
         (ww (csm:buf-width scr))
         (wh (csm:buf-height scr))
         (line (make-string ww csm:chr)))
    (loop for y from 0 below wh 
          with bpos = (point-min)
          with spos = 0
          do
          (loop for x from 0 below ww
                do
                (put-text-property 
                 bpos (1+ bpos) 'face 
                 (csm:screen-color (aref tbuf spos) (aref zbuf spos))
                 buf)
                (incf bpos) (incf spos))
          (incf bpos) ; line separator
          )))

(defun csm:update-mode-line (&optional msg)
  (let* ((world d3m-world)
         (pos (mt:sxv 0.1 (csm:fromfxv (csm:world-pos world))))
         (map (csm:world-map world))
         (msg-line (if msg (list "---" msg))))
    (setq mode-line-format 
          `("-" mode-line-mule-info
            " " 
            ,(format "Pos: (%3.1f, %3.1f)"
                     (mt:vref pos 0) (mt:vref pos 1))
            ,@msg-line
            "-%-"))
    (force-mode-line-update)))

(defun csm:update-buffer (buf world)
  (let ((start-time (float-time)) map-time bitblt-time gc-time fin-time)
  (csm:draw-world world)
  (setq map-time (float-time))
  (csm:draw-2dmap world)
  (setq bitblt-time (float-time))
  (csm:screen-bitblt buf world)
  (setq gc-time (float-time))
  (garbage-collect)
  (setq fin-time (float-time))
  (csm:update-mode-line 
   (format "[geo:%2.3f map:%2.3f bitblt:%2.3f gc:%2.3f"
           (- map-time start-time)
           (- bitblt-time map-time)
           (- gc-time bitblt-time)
           (- fin-time gc-time)))))


;;==================================================

;; バッファローカル変数
;; d3m-command-event : キー入力の指示内容
;; d3m-event-status  : 処理中 csm:state-busy, 入力待ち csm:state-wait

(defun csm:post-event-task (event)
  "非同期に実行させたいイベントを登録する。最後にpostされたものだけが残る"
  (let ((buf (get-buffer csm:buffer-main)))
    (when buf
      (with-current-buffer buf
        (if (or 
             (null d3m-command-event) ;; 何もなければ登録
             (and d3m-command-event ;; update(再描画)イベントは上書きしない
                  (not (eq event 'csm:explorer-update))))
            (setq d3m-command-event event))
        (csm:explorer-command-event-task)))))

(defun csm:explorer-command-event-task ()
  "d3m-command-event を読み取って実行する"
  ;;(message "TASK")
  (when (and d3m-command-event
             (eq d3m-event-status 'csm:state-wait))
    (lexical-let ((buf (current-buffer)))
      (deferred:try
        (deferred:$
          (deferred:next
            (lambda (x) 
              (with-current-buffer buf
                (setq d3m-event-status 'csm:state-busy)
                (let ((command d3m-command-event))
                  ;;(message "EXEC: %S" command)
                  (setq d3m-command-event nil)
                  (csm:explorer-command-exec command))))))
        :finally
        (lambda (x) 
          (cond
           ((buffer-local-value 'd3m-command-event buf)
            ;;(message "TRY NEXT: %S" d3m-command-event)
            (deferred:$
              (deferred:wait 50)
              (deferred:nextc it 
                (lambda (x) 
                  (with-current-buffer buf
                    (setq d3m-event-status 'csm:state-wait)
                    (csm:explorer-command-event-task))))))
           (t 
            ;;(message "FINISH:")
            (deferred:$
              (deferred:wait 40)
              (deferred:nextc it 
                (lambda (x) 
                  (with-current-buffer buf
                    (setq d3m-event-status 'csm:state-wait))))))))))))

(defun csm:explorer-command-exec (event)
  (when event
    (funcall event)))

(defun csm:explorer-move-gen (move turn)
  (let* ((world d3m-world)
         (buf (current-buffer))
         (pos-f (csm:world-pos world))
         (angle (csm:world-angle world))
         (npos-f (mt:v+v pos-f 
                         (csm:tofxv 
                          (mt:mxv 
                           (mt:mrot2d (csm:d2r angle)) move))))
         (nangle (csm:degree (+ angle turn))))
    (when (< 0 (logand (csm:draw-wall-find-object 
                        (csm:world-map world) npos-f)
                       csm:tbuf-floor))
      (csm:world-set-pos world npos-f))
    (csm:world-set-angle world nangle)
    (csm:server-send-move (csm:fromfxv npos-f) nangle)
    (csm:update-buffer buf world)))

(defvar csm:move-scale 2)
(defvar csm:turn-scale 15)

(defun csm:explorer-move-forward ()
  (interactive)
  (csm:explorer-move-gen (mt:vnew (vector csm:move-scale 0)) 0))

(defun csm:explorer-move-backward ()
  (interactive)
  (csm:explorer-move-gen (mt:vnew (vector (- csm:move-scale) 0)) 0))

(defun csm:explorer-move-left ()
  (interactive)
  (csm:explorer-move-gen (mt:vnew (vector 0 (- csm:move-scale))) 0))

(defun csm:explorer-move-right ()
  (interactive)
  (csm:explorer-move-gen (mt:vnew (vector 0 csm:move-scale)) 0))

(defun csm:explorer-turn-left ()
  (interactive)
  (csm:explorer-move-gen (mt:vnew [0 0]) (- csm:turn-scale)))

(defun csm:explorer-turn-right ()
  (interactive)
  (csm:explorer-move-gen (mt:vnew [0 0]) csm:turn-scale))

(defun csm:explorer-turn-back ()
  (interactive)
  (csm:explorer-move-gen (mt:vnew [0 0]) 180))

(defun csm:explorer-update ()
  (csm:update-buffer (current-buffer) d3m-world))


;;==================================================

(defvar csm:explorer-mode-map 
  (csm:define-keymap
   '(
     ("<up>"    . csm:command-move-forward)
     ("<down>"  . csm:command-move-backward)
     ("<left>"  . csm:command-turn-left)
     ("<right>" . csm:command-turn-right)
     ("a"       . csm:command-move-left)
     ("s"       . csm:command-move-right)
     ("b"       . csm:command-turn-back)
     ("m"       . csm:command-toggle-map)
     ("q"       . csm:command-quit)
     )))

(define-derived-mode csm:explorer-mode 
  fundamental-mode 
  "3D Maze Explorer mode"
  "3D Maze Explorer mode"
  (set (make-local-variable 'd3m-world) nil)
  (set (make-local-variable 'd3m-event-status) 'csm:state-wait)
  (set (make-local-variable 'd3m-command-event) nil)
  (setq buffer-read-only t))

(defun csm:command-toggle-map ()
  (interactive)
  (setq csm:2dmap-display (not csm:2dmap-display))
  (csm:post-event-task 'csm:explorer-update))

(defun csm:command-move-forward ()
  (interactive)
  (csm:post-event-task 'csm:explorer-move-forward))

(defun csm:command-move-backward ()
  (interactive)
  (csm:post-event-task 'csm:explorer-move-backward))

(defun csm:command-move-left ()
  (interactive)
  (csm:post-event-task 'csm:explorer-move-left))

(defun csm:command-move-right ()
  (interactive)
  (csm:post-event-task 'csm:explorer-move-right))

(defun csm:command-turn-left ()
  (interactive)
  (csm:post-event-task 'csm:explorer-turn-left))

(defun csm:command-turn-right ()
  (interactive)
  (csm:post-event-task 'csm:explorer-turn-right))

(defun csm:command-turn-back ()
  (interactive)
  (csm:post-event-task 'csm:explorer-turn-back))

(defun csm:command-update ()
  (interactive)
  (csm:post-event-task 'csm:explorer-update))

(defun csm:command-quit ()
  (interactive)
  (setq d3m-command-event nil)
  (when (get-buffer csm:buffer-main)
    (kill-buffer csm:buffer-main))
  (csm:server-disconnect))


;;==================================================

(defun csm:client-start ()
  (interactive)
  (csm:log-init)
  (csm:dialog-startup))

;; (global-set-key (kbd "M-0") 'csm:client-start)

;; (eval-current-buffer)
;; (csm:log-init)
;; (csm:connect-server csm:dialog-value-name "liza2.local" csm:dialog-value-port)
;; (setq csm:debug-out nil)
;; (setq csm:debug-out t)
;; (list-processes)

(provide 'client-maze)
;;; client-maze.el ends here
