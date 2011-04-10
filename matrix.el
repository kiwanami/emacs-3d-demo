(require 'cl)

;;; Vector

(defstruct mt:v dim x)

(defsubst mt:vnew (elms)
  (make-mt:v :dim (length elms) :x elms))

(defsubst mt:vcp (v)
  (mt:vnew (vconcat (mt:v-x v))))

;; getter and setter

(defsubst mt:vref (v i)
  (aref (mt:v-x v) i))

(defsubst mt:vset (v i a)
  (aset (mt:v-x v) i a))

(defun mt:vset2d (v x y)
  (let ((ar (mt:v-x v)))
    (aset ar 0 x) (aset ar 1 y) v))

;; scalar multiply

(defun mt:sxv (s v)
  "scalar multiply. return new value."
  (loop for i from 0 below (mt:v-dim v)
        with r = (mt:vcp v)
        do (mt:vset r i (* s (mt:vref v i)))
        finally return r))

(defun mt:sxv2d (s v)
  (let ((ar (mt:v-x v)))
    (make-mt:v 
     :dim 2
     :x (vector (* s (aref ar 0))
                (* s (aref ar 1))))))

(defun mt:sxv= (s v)
  "scalar multiply. return value."
  (loop for i from 0 below (mt:v-dim v)
        do (mt:vset v i (* s (mt:vref v i)))
        finally return v))

(defun mt:sxv2d= (s v)
  (let ((ar (mt:v-x v)))
    (aset ar 0 (* s (aref ar 0)))
    (aset ar 1 (* s (aref ar 1))))
  v)

;; add and subtract

(defun mt:vbin (op a b)
  "binary operator. return new value."
  (let ((r (mt:vcp a)) (dim (mt:v-dim a)))
    (loop for i from 0 below dim
          do (mt:vset r i (funcall op (mt:vref a i) (mt:vref b i))))
    r))

(defun mt:vbin= (op a b)
  "binary operator. substitute a."
  (let ((dim (mt:v-dim a)))
    (loop for i from 0 below dim
          do (mt:vset a i (funcall op (mt:vref a i) (mt:vref b i))))
    a))

(defmacro mt:def-vbin2d (name op)
  `(defun ,name (a b)
     (let ((aa (mt:v-x a)) (bb (mt:v-x b)))
       (make-mt:v 
        :dim 2 
        :x (vector (,op (aref aa 0) (aref bb 0))
                   (,op (aref aa 1) (aref bb 1)))))))

(defmacro mt:def-vbin2d= (name op)
  `(defun ,name (a b)
     (let ((aa (mt:v-x a)) (bb (mt:v-x b)))
       (aset aa 0 (,op (aref aa 0) (aref bb 0)))
       (aset aa 1 (,op (aref aa 1) (aref bb 1)))
       a)))

(defun mt:v+v (a b)
  "plus. return new value."
  (mt:vbin '+ a b))

(defun mt:v-v (a b)
  "minus. return new value."
  (mt:vbin '- a b))

(defun mt:v+v= (a b)
  "plus. substitute a."
  (mt:vbin= '+ a b))

(defun mt:v-v= (a b)
  "minus. substitute a."
  (mt:vbin= '- a b))

(mt:def-vbin2d  mt:v+v2d  +)
(mt:def-vbin2d  mt:v-v2d  -)
(mt:def-vbin2d= mt:v+v2d= +)
(mt:def-vbin2d= mt:v-v2d= -)

;; vector operations

(defun mt:vlen (a)
  "return a length of vector a."
  (let ((sq 0) (dim (mt:v-dim a)))
    (loop for i from 0 below dim
          for ii = (mt:vref a i)
          do (incf sq (* ii ii)))
    (sqrt (float sq))))

(defun mt:vlen2d (a)
  (let* ((aa (mt:v-x a))
         (ax (aref aa 0)) (ay (aref aa 1)))
    (sqrt (float (+ (* ax ax) (* ay ay))))))

(defun mt:vip (a b)
  "return inner product."
  (loop for i from 0 below (mt:v-dim a)
        with ret = 0 do
        (incf ret (* (mt:vref a i) (mt:vref b i)))
        finally return ret))

(defun mt:vop (a b)
  "return outer product."
  (cond
   ((and (eql (mt:v-dim a) 2) (eql (mt:v-dim b) 2))
    (- (* (mt:vref a 0) (mt:vref b 1)) (* (mt:vref a 1) (mt:vref b 0))))
   (t
    (error "Not supported outer product. %S %S" a b))))

(defun mt:vunit (a)
  "return new unit vector along the vector a."
  (mt:sxv (/ 1.0 (mt:vlen a)) a))

(defun mt:vnorm (a)
  (cond
   ((eql (mt:v-dim a) 2)
    (mt:vnew (vector (- (mt:vref a 1)) (mt:vref a 0))))
   (t
    (error "Not supported normal vector. %S" a))))

(defun mt:vzero (dim)
  (mt:vnew (make-vector dim 0)))

(defun mt:vfloor (a)
  (loop for i from 0 below (mt:v-dim a)
        do
        (mt:vset a i (floor (mt:vref a i)))
        finally return a))

(defun mt:vfloor2d (a)
  (let ((aa (mt:v-x a)))
    (aset aa 0 (floor (aref aa 0)))
    (aset aa 1 (floor (aref aa 1)))
    a))


;;; Matrix

(defstruct mt:m dim v)

(defun mt:mnew (dim elms)
  (make-mt:m :dim dim :v elms))

(defun mt:mcp (m)
  (make-mt:m :dim (mt:m-dim m) :v (vconcat (mt:m-v m))))

;; getter and setter

(defun mt:mref (m i j)
  (aref (mt:m-v m) (+ (* j (mt:m-dim m)) i)))

(defun mt:mset (m i j a)
  (aset (mt:m-v m) (+ (* j (mt:m-dim m)) i) a))

;; add and subtract

(defun mt:mbin (op a b)
  (let ((r (mt:mcp a)) (dim (mt:m-dim a)))
    (loop for i from 0 below dim do 
          (loop for j from 0 below dim do
                (mt:mset r i j 
                         (funcall op (mt:mref a i j) (mt:mref b i j)))))
    r))

(defun mt:mbin= (op a b)
  (let ((dim (mt:m-dim a)))
    (loop for i from 0 below dim do 
          (loop for j from 0 below dim do
                (mt:mset a i j 
                         (funcall op (mt:mref a i j) (mt:mref b i j)))))
    a))

(defun mt:m+m (a b)
  (mt:mbin '+ a b))

(defun mt:m-m (a b)
  (mt:mbin '- a b))

(defun mt:m+m= (a b)
  (mt:mbin= '+ a b))

(defun mt:m-m= (a b)
  (mt:mbin= '- a b))

;; multiply

(defun mt:mxm (a b)
  (let ((r (mt:mcp a)) (dim (mt:m-dim a)) s)
    (loop for i from 0 below dim do 
          (loop for j from 0 below dim do
                (setq s 0)
                (loop for k from 0 below dim 
                      for av = (mt:mref a k j)
                      for bv = (mt:mref b i k) do
                      (incf s (* av bv)))
                (mt:mset r i j s)))
    r))

(defun mt:sxm (s m)
  (let ((r (mt:mcp m)) (dim (mt:m-dim m)))
    (loop for i from 0 below dim do 
          (loop for j from 0 below dim do
                (mt:mset r i j (* s (mt:mref m i j)))))
    r))

(defun mt:sxm2d (s m)
  (let ((aa (mt:m-v m)))
    (make-mt:m 
     :dim 2 
     :v (vector 
         (* s (aref aa 0))
         (* s (aref aa 1))
         (* s (aref aa 2))
         (* s (aref aa 3))))))

(defun mt:sxm= (s m)
  (let ((dim (mt:m-dim m)))
    (loop for i from 0 below dim do 
          (loop for j from 0 below dim do
                (mt:mset m i j (* s (mt:mref m i j)))))
    m))

(defun mt:sxm2d= (s m)
  (let ((aa (mt:m-v m)))
    (aset aa 0 (* s (aref aa 0)))
    (aset aa 1 (* s (aref aa 1)))
    (aset aa 2 (* s (aref aa 2)))
    (aset aa 3 (* s (aref aa 3)))))

(defun mt:mxv (m v)
  "multiply matrix and vector. return new vector."
  (let ((r (mt:vcp v)) (dim (mt:v-dim v)))
    (loop for i from 0 below dim
          do (mt:vset r i 
                      (loop for j from 0 below dim
                            with s = 0
                            do (incf s (* (mt:vref v j) (mt:mref m j i)))
                            finally return s)))
    r))

(defun mt:vxm (v m)
  "multiply matrix and vector. return new vector."
  (let ((r (mt:vcp v)) (dim (mt:v-dim v)))
    (loop for i from 0 below dim
          do (mt:vset r i 
                      (loop for j from 0 below dim
                            with s = 0
                            do (incf s (* (mt:vref v j) (mt:mref m i j)))
                            finally return s)))
    r))

(defun mt:mxv2d (m v)
  (let* ((mm (mt:m-v m)) (vv (mt:v-x v))
         (v1 (aref vv 0)) (v2 (aref vv 1)))
    (make-mt:v
     :dim 2
     :x (vector
         (+ (* v1 (aref mm 0)) (* v2 (aref mm 1)))
         (+ (* v1 (aref mm 2)) (* v2 (aref mm 3)))))))

(defun mt:vxm2d (v m)
  (let* ((mm (mt:m-v m)) (vv (mt:v-x v))
         (v1 (aref vv 0)) (v2 (aref vv 1)))
    (make-mt:v
     :dim 2
     :x (vector
         (+ (* v1 (aref mm 0)) (* v2 (aref mm 2)))
         (+ (* v1 (aref mm 1)) (* v2 (aref mm 3)))))))

(defun mt:mxv= (m v r)
  "multiply matrix and vector. return new vector."
  (let ((dim (mt:v-dim v)))
    (loop for i from 0 below dim
          do (mt:vset r i 
                      (loop for j from 0 below dim
                            with s = 0
                            do (incf s (* (mt:vref v j) (mt:mref m j i)))
                            finally return s)))
    r))

(defun mt:vxm= (v m r)
  "multiply matrix and vector. return new vector."
  (let ((dim (mt:v-dim v)))
    (loop for i from 0 below dim
          do (mt:vset r i 
                      (loop for j from 0 below dim
                            with s = 0
                            do (incf s (* (mt:vref v j) (mt:mref m i j)))
                            finally return s)))
    r))

(defun mt:mxv2d= (m v r)
  (let* ((mm (mt:m-v m)) (vv (mt:v-x v)) (rr (mt:v-x r))
         (v1 (aref vv 0)) (v2 (aref vv 1)))
    (aset rr 0 (+ (* v1 (aref mm 0)) (* v2 (aref mm 1))))
    (aset rr 1 (+ (* v1 (aref mm 2)) (* v2 (aref mm 3))))
    r))

(defun mt:vxm2d= (v m r)
  (let* ((mm (mt:m-v m)) (vv (mt:v-x v)) (rr (mt:v-x r))
         (v1 (aref vv 0)) (v2 (aref vv 1)))
    (aset rr 0 (+ (* v1 (aref mm 0)) (* v2 (aref mm 2))))
    (aset rr 1 (+ (* v1 (aref mm 1)) (* v2 (aref mm 3))))
    r))

;; matrix utility

(defun mt:mzero (dim)
  (mt:mnew dim (make-vector (* dim dim) 0)))

(defun mt:munit (dim)
  (let ((ret (mt:mzero dim)))
    (loop for i from 0 below dim do
          (mt:mset ret i i 1))
    ret))

(defun mt:mrot2d (rad)
  (let ((c (cos rad)) (s (sin rad)))
    (mt:mnew 
     2 (vector c (- s) s c))))

(defun mt:mfloor (a)
  (let* ((ar (mt:m-v a)) (len (length ar)))
    (loop for i from 0 below len
          do
          (aset ar i (floor (aref ar i)))
          finally return a)))

(defun mt:mfloor2d (a)
  (let* ((ar (mt:m-v a)))
    (aset ar 0 (floor (aref ar 0)))
    (aset ar 1 (floor (aref ar 1)))
    (aset ar 2 (floor (aref ar 2)))
    (aset ar 3 (floor (aref ar 3)))
    a))


;;; test

(defvar mt:test-counter nil)

(defun mt:begin-test ()
  (when (get-buffer "*matrix:test*")
    (kill-buffer "*matrix:test*"))
  (setq mt:test-counter (cons 0 0)))

(defun mt:end-test ()
  (mt:test-output
   (format "--------------------\nPass: %s  Error: %s"
           (car mt:test-counter) (cdr mt:test-counter))))

(defun mt:test-output (msg)
  (pop-to-buffer "*matrix:test*")
  (goto-char (point-max))
  (insert msg "\n"))

(defun mt:ok (msg left right)
  (cond
   ((equal left right)
    (mt:test-output (format "OK: %s" msg))
    (incf (car mt:test-counter)))
   (t
    (mt:test-output
     (let ((text (format "NG: %s  :  %S  :  %S" msg left right)))
       (put-text-property 0 (length text) 'face 'compilation-error text)
       text))
    (incf (cdr mt:test-counter)))))

(defun mt:test ()
  (interactive)
  (mt:begin-test)

  ;; vector - vector
  (let* ((a (mt:vnew [1 2])) (al (sqrt 5))
         (b (mt:vnew [3 -1])))
    (mt:ok "v+v" (mt:v+v a b) (mt:vnew [4 1]))
    (mt:ok "v-v" (mt:v-v a b) (mt:vnew [-2 3]))
    (mt:ok "sxv" (mt:sxv 4 a) (mt:vnew [4 8]))
    (mt:ok "v+v=" (mt:v+v= (mt:vcp a) b) (mt:vnew [4 1]))
    (mt:ok "v-v=" (mt:v-v= (mt:vcp a) b) (mt:vnew [-2 3]))
    (mt:ok "sxv=" (mt:sxv= 4 (mt:vcp a)) (mt:vnew [4 8]))
    (mt:ok "vip" (mt:vip a b) 1)
    (mt:ok "vop" (mt:vop a b) -7)
    (mt:ok "vlen" (mt:vlen a) al)
    (mt:ok "vunit" (mt:vunit a) (mt:vnew (vector (/ 1.0 al) (/ 2 al))))
    (mt:ok "vnorm" (mt:vnorm a) (mt:vnew (vector -2 1 )))
    (mt:ok "vip norm" (mt:vip a (mt:vnorm a)) 0)
    (mt:ok "vzero" (mt:vzero 2) (mt:vnew [0 0]))
    (mt:ok "vfloor" (mt:vfloor (mt:vnew [0.1 1.1])) (mt:vnew [0 1]))
    )

  ;; 2D / vector - vector
  (let* ((a (mt:vnew [1 2])) (al (sqrt 5))
         (b (mt:vnew [3 -1])))
    (mt:ok "v+v2d" (mt:v+v2d a b) (mt:vnew [4 1]))
    (mt:ok "v-v2d" (mt:v-v2d a b) (mt:vnew [-2 3]))
    (mt:ok "sxv2d" (mt:sxv2d 4 a) (mt:vnew [4 8]))
    (mt:ok "v+v2d=" (mt:v+v2d= (mt:vcp a) b) (mt:vnew [4 1]))
    (mt:ok "v-v2d=" (mt:v-v2d= (mt:vcp a) b) (mt:vnew [-2 3]))
    (mt:ok "sxv2d=" (mt:sxv2d= 4 (mt:vcp a)) (mt:vnew [4 8]))
    (mt:ok "vlen2d" (mt:vlen2d a) al)
    (mt:ok "vfloor2d" (mt:vfloor2d (mt:vnew [0.1 1.1])) (mt:vnew [0 1]))
    )

  ;; matrix - matrix
  (let* ((a (mt:mnew 2 [1 2 3 4]))
         (b (mt:mnew 2 [5 6 7 8]))
         (c (mt:mnew 2 [7 6 3 2])))
    (mt:ok "m+m1" (mt:m+m a b) (mt:mnew 2 [6 8 10 12]))
    (mt:ok "m-m1" (mt:m-m a b) (mt:mnew 2 [-4 -4 -4 -4]))
    (mt:ok "m+m2" (mt:m+m a c) (mt:mnew 2 [8 8 6 6]))
    (mt:ok "m-m2" (mt:m-m a c) (mt:mnew 2 [-6 -4 0 2]))
    (mt:ok "m+m=1" (mt:m+m (mt:mcp a) b) (mt:mnew 2 [6 8 10 12]))
    (mt:ok "m-m=1" (mt:m-m (mt:mcp a) b) (mt:mnew 2 [-4 -4 -4 -4]))
    (mt:ok "sxm" (mt:sxm 2 a) (mt:mnew 2 [2 4 6 8]))
    (mt:ok "sxm=" (mt:sxm 2 (mt:mcp a)) (mt:mnew 2 [2 4 6 8]))
    (mt:ok "mxm1" (mt:mxm a b) (mt:mnew 2 [19 22 43 50]))
    (mt:ok "mxm2" (mt:mxm a c) (mt:mnew 2 [13 10 33 26]))
    (mt:ok "munit" (mt:munit 2) (mt:mnew 2 [1 0 0 1]))
    (mt:ok "mzero" (mt:mzero 2) (mt:mnew 2 [0 0 0 0]))
    (mt:ok "mfloor" (mt:mfloor (mt:mnew 2 [0.1 -0.1 1.1 -1.1])) (mt:mnew 2 [0 -1 1 -2])))

  ;; 2D matrix - matrix
  (let* ((a (mt:mnew 2 [1 2 3 4]))
         (b (mt:mnew 2 [5 6 7 8]))
         (c (mt:mnew 2 [7 6 3 2])))
    (mt:ok "sxm/2d" (mt:sxm2d 2 a) (mt:mnew 2 [2 4 6 8]))
    (mt:ok "sxm=/2d" (mt:sxm2d 2 (mt:mcp a)) (mt:mnew 2 [2 4 6 8]))
    (mt:ok "mfloor/2d" (mt:mfloor2d (mt:mnew 2 [0.1 -0.1 1.1 -1.1])) (mt:mnew 2 [0 -1 1 -2])))

  ;;matrix - vector
  (let* ((m1 (mt:mnew 2 [1 -2 5 3]))
         (m2 (mt:mnew 2 [3 1 -2 7]))
         (v1 (mt:vnew [2 3])))
    (mt:ok "mxm " (mt:mxm m1 m2) (mt:mnew 2 [7 -13 9 26]))
    (mt:ok "mxv1" (mt:mxv m1 v1) (mt:vnew [-4 19]))
    (mt:ok "vxm1" (mt:vxm v1 m1) (mt:vnew [17 5]))
    (mt:ok "mxv=1" (mt:mxv= m1 v1 (mt:vcp v1)) (mt:vnew [-4 19]))
    (mt:ok "vxm=1" (mt:vxm= v1 m1 (mt:vcp v1)) (mt:vnew [17 5]))
    (mt:ok "mxv2" (mt:mxv m2 v1) (mt:vnew [9 17]))
    (mt:ok "vxm2" (mt:vxm v1 m2) (mt:vnew [0 23])))

  ;; 2D matrix - vector
  (let* ((m1 (mt:mnew 2 [1 -2 5 3]))
         (m2 (mt:mnew 2 [3 1 -2 7]))
         (v1 (mt:vnew [2 3])))
    (mt:ok "mxv1/2d" (mt:mxv2d m1 v1) (mt:vnew [-4 19]))
    (mt:ok "vxm1/2d" (mt:vxm2d v1 m1) (mt:vnew [17 5]))
    (mt:ok "mxv=1/2d" (mt:mxv2d= m1 v1 (mt:vcp v1)) (mt:vnew [-4 19]))
    (mt:ok "vxm=1/2d" (mt:vxm2d= v1 m1 (mt:vcp v1)) (mt:vnew [17 5]))
    (mt:ok "mxv2/2d" (mt:mxv2d m2 v1) (mt:vnew [9 17]))
    (mt:ok "vxm2/2d" (mt:vxm2d v1 m2) (mt:vnew [0 23])))

  (mt:end-test))

;; (progn (eval-current-buffer) (mt:test))

(provide 'matrix)
