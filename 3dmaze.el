;;; 3dmaze.el --- 3D maze explorer

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

;; TODO:
;; 読み書き禁止
;; 時間差描画

;; デモなので効率優先。
;; なるべくチェックを省くため、パラメーター、計算式の妥当性はプログラマの責任。
;; 整数、小数、defstruct、型エラー、配列範囲エラーをコンパイルエラーと思ってバグ発見する。

;; 単位系まとめ
;; 角度： 基本 degree 整数 0-359。ローカル内でradianや小数で扱っても良い。
;; 位置： 基本 マップ上の1文字が d3m:scale となるサイズの長さで扱う。
;;   基本座標系：↑
;;   マップ座標系：マップ上の文字のインデックスに対応する座標、整数。
;;   固定小数座標系：基本座標系に d3m:fx をかけて整数で扱う。
;;         整数演算をするため、乗除、演算順序に注意。変数の後ろに -f をつけて表す。
;;   スクリーン座標系：d3m:buf構造体で保持する幅と高さの整数。zバッファは固定小数座標系での距離。


;;; Code:

(require 'cl)
(require 'derived)
(require 'concurrent)
(require 'matrix)

(defstruct d3m:map width height map objects)
(defstruct d3m:buf width height tbuf zbuf)
(defstruct d3m:pos x y)
(defstruct d3m:object def pos)

;; 全体の見え方に対するパラメーター
(defvar d3m:scale 10.0 "MAP上の1文字のサイズ。壁の高さ。")
(defvar d3m:aperture-size 30.0 "描画すべき画角。単位degree。")

;; d3m:map-tbuf に入れるオブジェクトのタイプ
(defconst d3m:tbuf-none    00)
(defconst d3m:tbuf-air     01)
(defconst d3m:tbuf-floor   02)
(defconst d3m:tbuf-floor2  03)
(defconst d3m:tbuf-wall    04)
(defconst d3m:tbuf-out     08)
(defconst d3m:tbuf-other   16)
(defconst d3m:tbuf-me      64)

(defconst d3m:zbuf-inf    1e10 "Zバッファの無限遠")
(defvar   d3m:zbuf-fogout  80.0 "fogで完全に消えてしまう距離（d3m:zlimitよりも遠い方が良い）")
(defvar   d3m:zlimit       60.0 "スキャン打ち切り距離")

(defconst d3m:chr  ?\  "bufferに実際にinsertする文字")

(defvar d3m:debug-out nil)
(defvar d3m:debug-buffer "*maze log*")

(defun d3m:log-init ()
  (when (get-buffer d3m:debug-buffer)
    (kill-buffer d3m:debug-buffer)))

(defun d3m:log (&rest args)
  (when d3m:debug-out
    (with-current-buffer
        (get-buffer-create d3m:debug-buffer)
      (buffer-disable-undo)
      (insert (apply 'format args) "\n"))))

(defun d3m:define-keymap (keymap-list)
  (let ((map (make-sparse-keymap)))
    (mapc 
     (lambda (i)
       (define-key map
         (if (stringp (car i))
             (read-kbd-macro (car i)) (car i))
         (cdr i)))
     keymap-list)
    map))

(defun d3m:str2map (src)
  (let* ((lines (split-string src "\n"))
         (width (loop for i in lines maximize (length i)))
         (height (length lines))
         (ret (make-vector (* width height) 0))
         objects)
    (loop for line in lines
          for j from 0 below (length lines)
          do 
          (loop for c across line
                for s = (char-to-string c)
                for i from 0 below (length line)
                for idx = (+ i (* width j))
                do
                (aset ret idx 
                      (if (or (eql c ?#) (eql c ?*)) 1 0))
                (when (string-match
                       "[a-zA-Z0-9();:{}<>?!@$%&=+-~]" s)
                  (push 
                   (make-d3m:object
                    :def (d3m:object-get s)
                    :pos 
                    (mt:sxv d3m:scale
                            (mt:v+v
                             (mt:vnew [0.5 0.5])
                             (mt:vnew (vector i j)))))
                   objects))
                (incf idx)))
    (make-d3m:map :width width :height height 
                  :map ret :objects objects)))

(defun d3m:world-new (map screen pos angle)
  (list map screen pos angle))

(defsubst d3m:world-map (world)
  (car world))

(defsubst d3m:world-screen (world)
  (cadr world))

(defsubst d3m:world-pos (world)
  (nth 2 world))

(defsubst d3m:world-set-pos (world pos)
  (setf (nth 2 world) pos))

(defsubst d3m:world-angle (world)
  (nth 3 world))

(defsubst d3m:world-set-angle (world angle)
  (setf (nth 3 world) angle))

(defsubst d3m:d2r (deg)
  (/ (* pi deg) 180.0))

(defsubst d3m:degree (d)
  (setq d (floor d))
  (cond
   ((< d 0) (+ d 360))
   ((>= d 360) (- d 360))
   (t d)))

;; 固定小数点演算を仮定
;; 値を1024倍して保持しておく
;; 固定小数点の変数は -f をつける
;; 30bit整数まで扱えるので、掛け算1回ぐらいならオーバーフローしないはず

(defvar d3m:fx 1024.0 "固定小数基数")
(defvar d3m:fxi 1024 "固定小数基数")

(defsubst d3m:tofx (v)
  (floor (* v d3m:fx)))

(defsubst d3m:fromfx (v)
  (/ v d3m:fx))

(defsubst d3m:tofxv (v)
  (mt:vfloor2d (mt:sxv2d d3m:fx v)))

(defsubst d3m:fromfxv (v)
  (mt:sxv2d (/ 1.0 d3m:fx) v))

(defvar d3m:table-num 360 "三角関数テーブルの要素数。1度1つで360個。")

(defun d3m:table-init (func)
  (loop for i from 0 below d3m:table-num
        with array = (make-vector d3m:table-num 0)
        do (aset array i 
                 (d3m:tofx 
                  (min 1048576 ;1024*1024
                       (funcall func (d3m:d2r i)))))
        finally return array))

(defvar d3m:table-sin (d3m:table-init 'sin) "三角関数テーブル sin")
(defvar d3m:table-cos (d3m:table-init 'cos) "三角関数テーブル cos")
(defvar d3m:table-tan (d3m:table-init 'tan) "三角関数テーブル tab")

(defsubst d3m:sin-f (degree)
  (aref d3m:table-sin degree))

(defsubst d3m:cos-f (degree)
  (aref d3m:table-cos degree))

(defsubst d3m:tan-f (degree)
  (aref d3m:table-tan degree))

(defun d3m:init-table-scanz ()
  (vconcat 
   (loop with zf = (d3m:tofx 1)
         until (> zf (d3m:tofx d3m:zlimit))
         collect
         (let ((ret zf))
           (cond
            ((< zf (/ (d3m:tofx d3m:scale) 2))
             (incf zf (/ (d3m:tofx d3m:scan-scale) 4)))
            ((< zf (d3m:tofx d3m:scale))
             (incf zf (/ (d3m:tofx d3m:scan-scale) 3)))
            ((< zf (d3m:tofx (* 2 d3m:scale)))
             (incf zf (d3m:tofx d3m:scan-scale)))
            (t 
             (incf zf (d3m:tofx (* 2 d3m:scan-scale)))))
           ret))))

(defvar d3m:scan-scale 1.6 "動径方向のスキャンサイズ単位")
(defvar d3m:table-scanz (d3m:init-table-scanz)
  "Zスキャンの距離配列。近くはきめ細かく、遠くは荒くを表現。")
;;(length d3m:table-scanz)


(defvar d3m:table-wall-num  80
  "距離→壁の高さを変換するテーブル（個数）")
(defvar d3m:table-wall-delta-f nil
  "距離→壁の高さを変換するテーブルの変換単位 ( zf / delta -> index )
 FIXME: should be buffer local")
(defvar d3m:table-wall nil "距離→壁の高さを変換するテーブル。
スクリーン高さに依存するのでバッファ初期化時に決まる。
 FIXME: should be buffer local")

(defun d3m:init-table-wall (window-height)
  (setq d3m:table-wall-delta-f (d3m:tofx (/ d3m:zlimit d3m:table-wall-num)))
  (setq d3m:table-wall
        (loop for i from 0 below d3m:table-wall-num
              with delta = (/ d3m:zlimit d3m:table-wall-num)
              with ret = (make-vector d3m:table-wall-num 0)
              for z = (* delta (max i 1))
              do (aset ret i (round (* (/ d3m:scale z) window-height 0.8)))
              finally return ret)))

(defsubst d3m:wall-f (zf)
  (let ((idx (/ zf d3m:table-wall-delta-f)))
    (cond
     ((< idx 0) (setq idx 0))
     ((>= idx d3m:table-wall-num)
      (setq idx (1- d3m:table-wall-num))))
    (aref d3m:table-wall idx)))


;;==================================================

(defun d3m:search-blank-pos (map)
  (loop with w = (d3m:map-width map)
        with h = (d3m:map-height map)
        for i from 0 to 1000 
        for x = (random w) for y = (random h)
        for idx = (+ x (* y w))
        do
        (when (= 0 (aref (d3m:map-map map) idx))
          (return (mt:vnew (vector x y))))
        finally return (mt:vnew (vector 1 1))))

(defun d3m:open-buffer (map &optional screen-width screen-height)
  (let ((buf (get-buffer-create "*3d maze*"))
        (scr (d3m:init-screen screen-width screen-height))
        world)
    (setq world 
          (d3m:world-new
           map scr 
           (d3m:tofxv
            (mt:sxv d3m:scale
                    (mt:v+v
                     (mt:vnew [0.5 0.5])
                     (d3m:search-blank-pos map))))
           90))
    (with-current-buffer buf
      (d3m:init-table-wall (d3m:buf-height scr))
      (d3m:explorer-mode)
      (buffer-disable-undo)
      (setq d3m-world world)
      (d3m:draw-world world)
      (d3m:init-buffer buf world)
      (d3m:update-buffer buf world))
    (switch-to-buffer buf)))

(defun d3m:init-screen (&optional screen-width screen-height)
  "裏画面バッファの準備"
  (let* ((ww (or screen-width (window-width)))
         (wh (or screen-height (window-height))))
    (make-d3m:buf :width ww :height wh
                  :tbuf (make-vector (* ww wh) d3m:tbuf-none)
                  :zbuf (make-vector (* ww wh) (d3m:tofx d3m:zbuf-inf)))))

(defun d3m:draw-world (world)
  (d3m:clear-screen (d3m:world-screen world))
  (d3m:draw-wall world)
  (d3m:draw-objects world)
  )
  

(defun d3m:clear-screen (scr)
  (fillarray (d3m:buf-tbuf scr) d3m:tbuf-none)
  (fillarray (d3m:buf-zbuf scr) (d3m:tofx d3m:zbuf-inf)))

(defun d3m:draw-wall (world)
  (let* ((scr (d3m:world-screen world)) (map (d3m:world-map world))
         (tbuf (d3m:buf-tbuf scr)) (zbuf (d3m:buf-zbuf scr))
         (ww (d3m:buf-width scr)) (wh (d3m:buf-height scr)) wwe
         (hww (/ ww 2)) (hwh (/ wh 2))
         (angle-f (d3m:tofx (d3m:world-angle world)))
         (pos-f (d3m:world-pos world))
         (posxf (mt:vref pos-f 0)) (posyf (mt:vref pos-f 1))
         (dt-f (/ (d3m:tofx d3m:aperture-size) hww))
         (zlimit-f (d3m:tofx d3m:zlimit))
         (start-f (d3m:tofx 1.0)) obj (rn-f (mt:vcp pos-f)))
    (setq wwe (- ww 1)) ; for loop step
    (loop for i from 0 below wwe by 2
          for px = (- i hww)
          for th = (d3m:degree (d3m:fromfx (+ angle-f (* dt-f px))))
          for cosf = (d3m:cos-f th) for sinf = (d3m:sin-f th)
          do
          ;;(d3m:log ">>> Scan way th: %04f  cosf: %S sinf: %S" th cosf sinf)
          (loop for zf across d3m:table-scanz
                do
                (mt:vset2d rn-f 
                           (+ posxf (/ (* zf cosf) d3m:fxi))
                           (+ posyf (/ (* zf sinf) d3m:fxi)))
                (setq obj (d3m:draw-wall-find-object map rn-f))
                ;;(d3m:log "Scan ?: %s  d: %04f rn: %S" obj zf rn-f)
                (cond
                 ((eq obj d3m:tbuf-wall)
                  (d3m:draw-wall-draw-wall i zf)
                  (d3m:draw-wall-draw-wall (1+ i) zf)
                  (return))
                 ((eq obj d3m:tbuf-out)
                  (d3m:draw-wall-draw-out i zf)
                  (d3m:draw-wall-draw-out (1+ i) zf)
                  (return))
                 (t 
                  (d3m:draw-wall-draw-floor i zf obj)
                  (d3m:draw-wall-draw-floor (1+ i) zf obj)))))))

(defun d3m:draw-wall-find-object (map v-f)
  (let* ((x (floor (d3m:fromfx (/ (mt:vref v-f 0) d3m:scale))))
         (y (floor (d3m:fromfx (/ (mt:vref v-f 1) d3m:scale)))))
    (cond
     ((or (< x 0) (< y 0)
          (>= x (d3m:map-width map))
          (>= y (d3m:map-height map)))
      d3m:tbuf-out)
     (t 
      (let* ((idx (+ x (* y (d3m:map-width map)))))
        (cond
         ((= 0 (aref (d3m:map-map map) idx))
          (if (< 0 (logand (+ x y) 1))
              d3m:tbuf-floor d3m:tbuf-floor2))
         (t d3m:tbuf-wall)))))))

(defun d3m:draw-wall-draw-wall (x z-f)
  (let* ((wall (d3m:wall-f z-f))
         (hwall (ceiling (/ wall 2.0)))
         (top (max 0 (- hwh hwall)))
         (btm (min (1- wh) (+ hwh hwall))))
    ;;(d3m:log "# x: %2s  z: %06f" x z-f)
    (loop for i from top to btm
          for idx = (+ x (* i ww))
          do
          (aset tbuf idx d3m:tbuf-wall)
          (aset zbuf idx z-f))))

(defun d3m:draw-wall-draw-out (x z-f)
  ;; DO NOTHING
  )

(defun d3m:draw-wall-draw-floor (x z-f obj)
  (let* ((wall (d3m:wall-f z-f))
         (hwall (/ wall 2))
         (btm (min wh (+ hwall hwh))))
    ;;(d3m:log "F x: %2s  z: %06f" x z-f)
    (loop for i from btm below wh
          for idx = (+ x (* i ww))
          for floorz = (aref zbuf idx)
          do
          (when (< z-f floorz)
            (aset tbuf idx obj)
            (aset zbuf idx z-f)))))

(defun d3m:draw-objects (world)
  (loop for obj in (d3m:map-objects 
                    (d3m:world-map world)) 
        do
        (d3m:draw-objects-one world obj)))

(defvar d3m:letter-def-table (make-hash-table :test 'equal)
  "文字 -> mapのハッシュ")

(defun d3m:object-get (chr)
  (let ((map (gethash chr d3m:letter-def-table)))
    (unless map
      (setq map (d3m:init-letter chr))
      (puthash chr map d3m:letter-def-table))
    map))

(defvar d3m:program-banner 
  (cond
   ((eq 'darwin system-type) "/usr/bin/banner")
   ((eq 'gnu/linux system-type) "/usr/bin/printerbanner")
   (t "banner"))
  "文字プログラム")

(defun d3m:init-letter (letter)
  (let* ((src 
          (with-temp-buffer
            (call-process d3m:program-banner nil t nil "-w" "40" letter)
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
    (make-d3m:map :width width :height height :map ret)))

(defun d3m:object-debug-out (object)
  (d3m:log-init)
  (with-current-buffer (get-buffer-create d3m:debug-buffer)
    (loop for y from 0 below (d3m:map-height object) do
          (loop for x from 0 below (d3m:map-width object) do
                (insert (if (= 1 (aref (d3m:map-map object) 
                                       (+ x (* y (d3m:map-width object)))))
                            "#" " ")))
          (insert "\n")))
  (pop-to-buffer d3m:debug-buffer))
;; (d3m:object-debug-out (d3m:init-letter "@"))

(defun d3m:draw-objects-one (world object)
  (let*
      ((scr (d3m:world-screen world)) (map (d3m:world-map world))
       (tbuf (d3m:buf-tbuf scr)) (zbuf (d3m:buf-zbuf scr))
       (ww (d3m:buf-width scr)) (wh (d3m:buf-height scr))
       (hww (/ ww 2)) (hwh (/ wh 2))
       (angle (d3m:world-angle world))
       (posv (mt:sxv2d (/ 1.0 d3m:fx) (d3m:world-pos world)))
       (tposv (d3m:object-pos object))
       (relv (mt:v-v2d tposv posv))
       (rad (atan (mt:vref relv 1) (mt:vref relv 0)))
       (degree (d3m:degree (- angle (* 180 (/ rad pi)))))
       (vlen (mt:vlen2d relv))
       (aplimit (* 1.6 d3m:aperture-size))
       (dw (/ wh d3m:aperture-size)) cx)
    (cond
     ((and (<= 0 degree) (< degree aplimit))
      (setq cx (floor (- hww (* dw degree)))))
     ((and (< (- 360 aplimit) degree) (< degree 360))
      (setq cx (floor (+ hww (* dw (- 360 degree)))))))
    (when (or (< vlen 3.0) (> vlen d3m:zlimit)) (setq cx nil))
    ;;(message "deg: %s  dist: %2.3f  cx: %s" degree vlen cx)
    (when cx
      (let* ((def (d3m:object-def object))
             (lw (d3m:map-width def))
             (lh (d3m:map-height def))
             (lmap (d3m:map-map def))
             (hlw (/ lw 2)) (hlh (/ lh 2))
             (delta (* (/ d3m:scale vlen) (/ d3m:scale hlw))) ; 文字サイズ調整（適当）
             (vlenf (d3m:tofx vlen)))
        (loop for ly from 0 below lh
              for scry = (floor (+ (* 1.2 hwh) (* delta (- ly hlh)))) do
              (loop for lx from 0 below lw 
                    for scrx = (floor (+ cx (* delta (- lx hlw))))
                    for scridx = (+ scrx (* ww scry))
                    for sczf = (if (and (<= 0 scrx) (< scrx ww) (<= 0 scry) (< scry wh))
                                   (aref zbuf scridx))
                    for val = (aref lmap (+ lx (* ly lw))) do
                    (when (and sczf (= 1 val) (< vlenf sczf))
                      (aset tbuf scridx object)
                      (aset zbuf scridx vlenf))))))))


;;==================================================

(defvar d3m:2dmap-display t "display switch 2D map")
(defvar d3m:2dmap-radial  3.0  "map size")
(defvar d3m:2dmap-rect-left   0.7 "left-top (0.0-1.0)")
(defvar d3m:2dmap-rect-top    0.0 "left-top (0.0-1.0)")
(defvar d3m:2dmap-rect-width  0.3 "width  (0.0-1.0)")
(defvar d3m:2dmap-rect-height 0.3 "height (0.0-1.0)")

(defun d3m:draw-2dmap (world)
  (when d3m:2dmap-display
    (let*
        ((scr (d3m:world-screen world)) (map (d3m:world-map world))
         (lmap (d3m:map-map map))
         (mapw (d3m:map-width map)) (maph (d3m:map-height map))
         (tbuf (d3m:buf-tbuf scr)) (zbuf (d3m:buf-zbuf scr))
         (ww (d3m:buf-width scr)) (wh (d3m:buf-height scr))
         (angle (d3m:world-angle world))
         (posv (mt:sxv2d (/ 1.0 d3m:fx) (d3m:world-pos world)))
         (scrx (floor (* ww d3m:2dmap-rect-left)))
         (scry (floor (* wh d3m:2dmap-rect-top)))
         (scrw (floor (* ww d3m:2dmap-rect-width))) (scrwe (1- scrw)) ; for loop step 
         (scrh (floor (* wh d3m:2dmap-rect-height)))
         (scrhw (/ scrw 2)) (scrhh (/ scrh 2))
         (scrxe (+ scrx scrw)) (scrye (+ scry scrh))
         (rot (mt:mrot2d (d3m:d2r (+ angle 90))))
         )
      ;;(d3m:log "=====================")
      (loop for scryi from 0 below scrh
            for scryii = (- scryi scrhh)
            with basev0 = (mt:vnew [0 0])
            do
            (loop for scrxi from 0 below scrwe by 2
                  for scrxii = (- scrxi scrhw)
                  for basev = (mt:vset2d 
                               basev0
                               (* d3m:2dmap-radial scrxii) 
                               (* 2 d3m:2dmap-radial scryii))
                  for mapv = (mt:v+v2d= (mt:mxv2d rot basev) posv)
                  for mapx = (floor (/ (mt:vref mapv 0) d3m:scale))
                  for mapy = (floor (/ (mt:vref mapv 1) d3m:scale))
                  for idx = 
                  (if (and (<= 0 mapx) (< mapx mapw)
                           (<= 0 mapy) (< mapy maph))
                      (+ mapx (* mapy mapw)) nil)
                  for val = (if idx (aref lmap idx) nil)
                  for scridx = (+ scrxi scrx (* ww (+ scry scryi)))
                  for vlenz = (d3m:tofx (mt:vlen2d basev))
                  do 
                  ;;(d3m:log "mapx:%s  mapy:%s  idx:%s  val:%s" mapx mapy idx val)
                  (cond
                   ((and (= 0 scrxii) (= 0 scryii))
                    (aset tbuf scridx d3m:tbuf-me)
                    (aset zbuf scridx vlenz)
                    (aset tbuf (1+ scridx) d3m:tbuf-me)
                    (aset zbuf (1+ scridx) vlenz))
                   ((null val) 
                    (aset tbuf scridx d3m:tbuf-out)
                    (aset zbuf scridx vlenz)
                    (aset tbuf (1+ scridx) d3m:tbuf-out)
                    (aset zbuf (1+ scridx) vlenz))
                   ((= 1 val)
                    (aset tbuf scridx d3m:tbuf-wall)
                    (aset zbuf scridx vlenz)
                    (aset tbuf (1+ scridx) d3m:tbuf-wall)
                    (aset zbuf (1+ scridx) vlenz))
                   (t
                    (aset tbuf scridx d3m:tbuf-floor)
                    (aset zbuf scridx vlenz)
                    (aset tbuf (1+ scridx) d3m:tbuf-floor)
                    (aset zbuf (1+ scridx) vlenz))))))))


;;==================================================

(defun d3m:init-buffer (buf world)
  "バッファに文字列を書き込み"
  (erase-buffer)
  (let* ((scr (d3m:world-screen world))
         (ww (d3m:buf-width scr))
         (wh (d3m:buf-height scr))
         (line (make-string ww d3m:chr)))
    (loop for i from 0 below wh do
          (insert line "\n"))
    (goto-char (point-min))
    (d3m:screen-bitblt buf world)))

(defstruct d3m:color-set num delta array)

(defun d3m:color-set-generate (base fog num)
  (let ((delta (/ d3m:zbuf-fogout num)) cl)
    (make-d3m:color-set
     :num num
     :delta (d3m:tofx delta)
     :array
     (vconcat
      (loop for i from 0 below num
            for d = (* delta i)
            for param = (/ (- d3m:zbuf-fogout d) d3m:zbuf-fogout)
            for cl =
            (cond
             ((< d3m:zbuf-fogout d) fog)
             ((< d 1.0) base)
             (t
              (mt:v+v 
               (mt:sxv param base)
               (mt:sxv (- 1.0 param) fog))))
            collect
            (list ':background
                  (format "#%2x%2x%2x" 
                          (mt:vref cl 0)
                          (mt:vref cl 1) 
                          (mt:vref cl 2))))))))

(defvar d3m:color-set-floor
  (d3m:color-set-generate (mt:vnew [130  71  51]) (mt:vnew [255 255 255]) 32))
(defvar d3m:color-set-floor2 
  (d3m:color-set-generate (mt:vnew [ 70  31  30]) (mt:vnew [255 255 255]) 32))
(defvar d3m:color-set-wall 
  (d3m:color-set-generate (mt:vnew [ 51  51 204]) (mt:vnew [255 255 255]) 32))
(defvar d3m:color-set-friend
  (d3m:color-set-generate (mt:vnew [ 90 255  90]) (mt:vnew [255 255 255]) 32))
(defvar d3m:color-set-other
  (d3m:color-set-generate (mt:vnew [255  90  90]) (mt:vnew [255 255 255]) 32))
(defvar d3m:color-default '(:background "white"))
(defvar d3m:color-out     '(:background "lightgray"))
(defvar d3m:color-me      '(:background "pink"))

(defun d3m:color-set-get (set z-f)
  (let* ((idx (/ z-f (d3m:color-set-delta set)))
         (array (d3m:color-set-array set)))
    (cond
     ((< idx 0) (aref array 0))
     ((< idx (d3m:color-set-num set))
      (aref array idx))
     (t (aref array (1- (length array)))))))

(defun d3m:screen-color (type z-f)
  (cond
   ((eq type d3m:tbuf-floor)  (d3m:color-set-get d3m:color-set-floor  z-f))
   ((eq type d3m:tbuf-floor2) (d3m:color-set-get d3m:color-set-floor2 z-f))
   ((eq type d3m:tbuf-wall)   (d3m:color-set-get d3m:color-set-wall   z-f))
   ((d3m:object-p type)       (d3m:color-set-get d3m:color-set-other  z-f))
   ((eq type d3m:tbuf-me)     d3m:color-me)
   ((eq type d3m:tbuf-out)    d3m:color-out)
   ((eq type d3m:tbuf-none)   d3m:color-default)
   (t  d3m:color-default)))

(defun d3m:screen-bitblt (buf world)
  "裏画面からバッファのテキストプロパティを書き換え"
  (let* ((map (d3m:world-map world))
         (scr (d3m:world-screen world))
         (tbuf (d3m:buf-tbuf scr))
         (zbuf (d3m:buf-zbuf scr))
         (ww (d3m:buf-width scr))
         (wh (d3m:buf-height scr))
         (line (make-string ww d3m:chr)))
    (loop for y from 0 below wh 
          with bpos = (point-min)
          with spos = 0
          do
          (loop for x from 0 below ww
                do
                (put-text-property 
                 bpos (1+ bpos) 'face 
                 (d3m:screen-color (aref tbuf spos)
                                   (aref zbuf spos))
                 buf)
                (incf bpos) (incf spos))
          (incf bpos) ; line separator
          )))

(defun d3m:update-mode-line (&optional msg)
  (let* ((world d3m-world)
         (pos (mt:sxv 0.1 (d3m:fromfxv (d3m:world-pos world))))
         (map (d3m:world-map world))
         (msg-line (if msg (list "---" msg))))
    (setq mode-line-format 
          `("-" mode-line-mule-info
            " " 
            ,(format "Pos: (%3.1f, %3.1f)"
                     (mt:vref pos 0) (mt:vref pos 1))
            ,@msg-line
            "-%-"))
    (force-mode-line-update)))

(defun d3m:update-buffer (buf world)
  (let ((start-time (float-time)) map-time bitblt-time gc-time fin-time)
  (d3m:draw-world world)
  (setq map-time (float-time))
  (d3m:draw-2dmap world)
  (setq bitblt-time (float-time))
  (d3m:screen-bitblt buf world)
  (setq gc-time (float-time))
  (garbage-collect)
  (setq fin-time (float-time))
  (d3m:update-mode-line 
   (format "[geo:%2.3f map:%2.3f bitblt:%2.3f gc:%2.3f"
           (- map-time start-time)
           (- bitblt-time map-time)
           (- gc-time bitblt-time)
           (- fin-time gc-time)))))


;;==================================================

;; バッファローカル変数
;; d3m-command-event : キー入力の指示内容
;; d3m-event-status  : 処理中 d3m:state-busy, 入力待ち d3m:state-wait

(defun d3m:explorer-command-event-task ()
  "d3m-command-event を読み取って実行する"
  ;;(message "TASK")
  (when (and d3m-command-event
             (eq d3m-event-status 'd3m:state-wait))
    (lexical-let ((buf (current-buffer)))
      (deferred:try
        (deferred:$
          (deferred:next
            (lambda (x) 
              (with-current-buffer buf
                (setq d3m-event-status 'd3m:state-busy)
                (let ((command d3m-command-event))
                  ;;(message "EXEC: %S" command)
                  (setq d3m-command-event nil)
                  (d3m:explorer-command-exec command))))))
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
                    (setq d3m-event-status 'd3m:state-wait)
                    (d3m:explorer-command-event-task))))))
           (t 
            ;;(message "FINISH:")
            (deferred:$
              (deferred:wait 40)
              (deferred:nextc it 
                (lambda (x) 
                  (with-current-buffer buf
                    (setq d3m-event-status 'd3m:state-wait))))))))))))

(defun d3m:explorer-command-exec (event)
  (when event
    (funcall event)))

(defun d3m:explorer-move-gen (move turn)
  (let* ((world d3m-world)
         (buf (current-buffer))
         (pos-f (d3m:world-pos world))
         (angle (d3m:world-angle world))
         (npos-f (mt:v+v pos-f 
                         (d3m:tofxv 
                          (mt:mxv 
                           (mt:mrot2d (d3m:d2r angle)) move))))
         (nangle (d3m:degree (+ angle turn))))
    (when (< 0 (logand (d3m:draw-wall-find-object 
                        (d3m:world-map world) npos-f)
                       d3m:tbuf-floor))
      (d3m:world-set-pos world npos-f))
    (d3m:world-set-angle world nangle)
    (d3m:update-buffer buf world)))

(defvar d3m:move-scale 2)
(defvar d3m:turn-scale 15)

(defun d3m:explorer-move-forward ()
  (interactive)
  (d3m:explorer-move-gen (mt:vnew (vector d3m:move-scale 0)) 0))

(defun d3m:explorer-move-backward ()
  (interactive)
  (d3m:explorer-move-gen (mt:vnew (vector (- d3m:move-scale) 0)) 0))

(defun d3m:explorer-move-left ()
  (interactive)
  (d3m:explorer-move-gen (mt:vnew (vector 0 (- d3m:move-scale))) 0))

(defun d3m:explorer-move-right ()
  (interactive)
  (d3m:explorer-move-gen (mt:vnew (vector 0 d3m:move-scale)) 0))

(defun d3m:explorer-turn-left ()
  (interactive)
  (d3m:explorer-move-gen (mt:vnew [0 0]) (- d3m:turn-scale)))

(defun d3m:explorer-turn-right ()
  (interactive)
  (d3m:explorer-move-gen (mt:vnew [0 0]) d3m:turn-scale))

(defun d3m:explorer-turn-back ()
  (interactive)
  (d3m:explorer-move-gen (mt:vnew [0 0]) 180))

(defun d3m:explorer-update ()
  (d3m:update-buffer (current-buffer) d3m-world))


;;==================================================

(defvar d3m:explorer-mode-map 
  (d3m:define-keymap
   '(
     ("<up>"    . d3m:command-move-forward)
     ("<down>"  . d3m:command-move-backward)
     ("<left>"  . d3m:command-turn-left)
     ("<right>" . d3m:command-turn-right)
     ("a"       . d3m:command-move-left)
     ("s"       . d3m:command-move-right)
     ("b"       . d3m:command-turn-back)
     ("m"       . d3m:command-toggle-map)
     )))

(define-derived-mode d3m:explorer-mode 
  fundamental-mode 
  "3D Maze Explorer mode"
  "3D Maze Explorer mode"
  (set (make-local-variable 'd3m-world) nil)
  (set (make-local-variable 'd3m-event-status) 'd3m:state-wait)
  (set (make-local-variable 'd3m-command-event) nil))

(defun d3m:command-toggle-map ()
  (interactive)
  (setq d3m:2dmap-display (not d3m:2dmap-display))
  (setq d3m-command-event 'd3m:explorer-update)
  (d3m:explorer-command-event-task))

(defun d3m:command-move-forward ()
  (interactive)
  (setq d3m-command-event 'd3m:explorer-move-forward)
  (d3m:explorer-command-event-task))

(defun d3m:command-move-backward ()
  (interactive)
  (setq d3m-command-event 'd3m:explorer-move-backward)
  (d3m:explorer-command-event-task))

(defun d3m:command-move-left ()
  (interactive)
  (setq d3m-command-event 'd3m:explorer-move-left)
  (d3m:explorer-command-event-task))

(defun d3m:command-move-right ()
  (interactive)
  (setq d3m-command-event 'd3m:explorer-move-right)
  (d3m:explorer-command-event-task))

(defun d3m:command-turn-left ()
  (interactive)
  (setq d3m-command-event 'd3m:explorer-turn-left)
  (d3m:explorer-command-event-task))

(defun d3m:command-turn-right ()
  (interactive)
  (setq d3m-command-event 'd3m:explorer-turn-right)
  (d3m:explorer-command-event-task))

(defun d3m:command-turn-back ()
  (interactive)
  (setq d3m-command-event 'd3m:explorer-turn-back)
  (d3m:explorer-command-event-task))


;;==================================================

(defun d3m:open-maze-buffer ()
  (interactive)
  (d3m:log-init)
  (setq d3m:debug-out nil)
  (let ((ww (min (window-width) 90)))
    (d3m:open-buffer
     (d3m:str2map (buffer-string))
     ww (/ ww 3))))

;; (global-set-key (kbd "M-0") 'd3m:open-maze-buffer)

;; (setq d3m:debug-out nil)
;; (setq d3m:debug-out t)

(defun d3m:test-exec ()
  (interactive)
  (d3m:log-init)
  (progn 
    (eval-current-buffer)
    (d3m:open-buffer
     (d3m:str2map "#####\n#S#G#\n#   #\n#####")
     30 10)))

(provide '3dmaze)
;;; 3dmaze.el ends here
