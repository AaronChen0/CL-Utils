(deftype u64 () '(unsigned-byte 64))
(deftype u32 () '(unsigned-byte 32))
(deftype u128 () '(unsigned-byte 128))
(defun squarep (n)
  (let ((sqrt (isqrt n)))
    (and (= (* sqrt sqrt) n) sqrt)))

(defun factorial (n)
  (do ((p 1))
      ((< n 2) p)
    (setf p (* p n) n (1- n))))

(defun permute (list)
  (if (null list) (list (list))
      (mapcan #'(lambda (x)
                  (mapcar #'(lambda (y) (cons x y))
                          (permute (remove x list))))
              list)))

(defun fib (n)
  (loop with (a b p q) = (list 1 0 0 1)
     if (zerop n) return b
     if (oddp n) do (psetf a (+ (* b q) (* a (+ p q)))
                           b (+ (* b p) (* a q)))
     do (psetf p (+ (* p p) (* q q))
               q (* q (+ q (* 2 p)))
               n (ash n -1))))

(defun exp-mod (b e m &aux (p 1))
  (setf b (mod b m))
  (loop if (zerop e) return p
     if (oddp e) do (setf p (mod (* p b) m))
     do (setf e (ash e -1) b (mod (* b b) m))))

(defun tonelli-shanks (n p)
  (when (zerop (mod n p)) (return-from tonelli-shanks (list 0)))
  (unless (= 1 (exp-mod n (floor (1- p) 2) p))
    (return-from tonelli-shanks nil))
  (let ((q (1- p)) (ss 0) (z 2))
    (loop while (evenp q) do (setf ss (1+ ss) q (ash q -1)))
    (when (= 1 ss)
      (let ((r1 (exp-mod n (floor (1+ p) 4) p)))
        (return-from tonelli-shanks (list r1 (- p r1)))))
    (loop with pp = (floor (1- p) 2)
       until (= (exp-mod z pp p) (1- p))
       do (incf z))
    (let ((c (exp-mod z q p))
          (r (exp-mod n (floor (1+ q) 2) p))
          (u (exp-mod n q p))
          (m ss))
      (loop (when (= u 1) (return (list r (- p r))))
         (let ((i 0) (zz u))
           (loop while (and (/= zz 1) (< i (1- m)))
              do (setf zz (mod (* zz zz) p) i (1+ i)))
           (let ((b c) (e (- m i 1)))
             (loop while (> e 0) do (setf b (mod (* b b) p) e (1- e)))
             (setf r (mod (* r b) p)
                   c (mod (* b b) p)
                   u (mod (* u c) p)
                   m i)))))))

(defun egcd (a b)
  (declare (fixnum a b))
  (loop with q fixnum
     for r1 fixnum = b then (- r2 (the fixnum (* r1 q)))
     and r2 fixnum = a then r1
     for s1 fixnum = 0 then (- s2 (the fixnum (* s1 q)))
     and s2 fixnum = 1 then s1
     for u1 fixnum = 1 then (- u2 (the fixnum (* u1 q)))
     and u2 fixnum = 0 then u1
     if (zerop r1) return (values r2 s2 u2)
     do (setf q (floor r2 r1))))

(defun invmod (a m)
  (multiple-value-bind (r s k) (egcd a m)
    (declare (ignore k))
    (unless (= 1 r)
      (error "invmod: Values ~a and ~a are not coprimes." a m))
    (mod s m)))

(defun chinese-remainder (rs ms)
  "Calculates the Chinese Remainder for the given set of integer
   modulo pairs. Note: All the Ms must be coprimes."
  (loop with mtot = (reduce '* ms)
     for r in rs
     for m in ms
     sum (* r (invmod (floor mtot m) m) (floor mtot m)) into s
     finally (return (mod s mtot))))

(defun c (n r)
  (setf r (min r (- n r)))
  (do ((prod 1) (i 1 (1+ i)))
      ((> i r) prod)
    (setf prod (floor (* prod n) i) n (1- n))))

(defun parse (n)
  (do (result)
      ((zerop n) (or result (list 0)))
    (multiple-value-bind (quotient remainder) (floor n 10)
      (push remainder result)
      (setf n quotient))))

(defun primep (n)
  (or (= n 2) (= n 3) (= n 5)
      (and (> n 1)
           (oddp n)
           (not (zerop (mod n 3)))
           (not (zerop (mod n 5)))
           (loop with k = 7
              with list = '#1=(4 2 4 2 4 6 2 6 . #1#)
              for i in list
              if (> (* k k) n) return t
              if (zerop (mod n k)) return nil
              do (incf k i)))))

(defun factor2 (n)
  (append
   (loop with limit = (isqrt n)
      for i in '(2 3 5)
      if (and (> i limit) (> n 1)) collect (list n 1) and do (setf n 1)
      until (= n 1)
      if (zerop (mod n i))
      collect (list i (loop for c from 1 do (setf n (floor n i))
                         unless (zerop (mod n i)) return c))
      and do (setf limit (isqrt n)))
   (loop with limit = (isqrt n)
      with i = 7
      with list = '#1=(4 2 4 2 4 6 2 6 . #1#)
      for k in list
      if (and (> i limit) (> n 1)) collect (list n 1) and do (setf n 1)
      until (= n 1)
      if (zerop (mod n i))
      collect (list i (loop for c from 1 do (setf n (floor n i))
                         unless (zerop (mod n i)) return c))
      and do (setf limit (isqrt n))
      do (incf i k))))

(defun factor (n)
  (mapcar #'car (factor2 n)))

(defun prime-count (n)
  (declare (optimize (speed 3) (debug 0) (safety 0))
           (u64 n))
  (let* ((sq (isqrt n))
         (pis (make-array (+ sq 1) :element-type 'u64))
         (pil (make-array (+ sq 1) :element-type 'u64)))
    (declare (u32 sq) ((simple-array u64) pis pil))
    (setf (aref pis 0) 0 (aref pil 0) 0)
    (loop for i of-type u32 from 1 to sq do (setf (aref pis i) (- i 1)))
    (loop for i of-type u32 from 1 to sq do (setf (aref pil i) (- (floor n i) 1)))
    (loop for p of-type u32 from 2 to sq
       if (/= (aref pis p) (aref pis (- p 1)))
       do (let ((pc (aref pis (- p 1))) (p2 (* p p)))
            (declare (u64 pc p2))
            (loop for i of-type u32 from 1 to (min sq (floor n p2))
               for d of-type u64 = (* i p)
               if (<= d sq) do (decf (aref pil i) (the u64 (- (aref pil d) pc)))
               else do (decf (aref pil i) (the u64 (- (aref pis (floor n d)) pc))))
            (loop for i of-type u32 downfrom sq to p2
               do (decf (aref pis i) (the u64 (- (aref pis (floor i p)) pc))))))
    (the fixnum (aref pil 1))))

(defun prime-sum (n)
  (declare (optimize (speed 3) (debug 0) (safety 0)) (u64 n)
           #+sbcl(sb-ext:muffle-conditions sb-ext:compiler-note))
  (let* ((r (isqrt n)) (ndr (floor n r)) (size (+ r ndr -1))
         (v (make-array size :element-type 'u64))
         (s (make-array size :element-type 'u128)))
    (declare (u64 r ndr size)
             ((simple-array u64) v) ((simple-array u128) s))
    (labels ((check (v n ndr size)
               (declare (u64 v n ndr size))
               (if (< v ndr) (- size v) (- (floor n v) 1))))
      (declare (inline check))
      (loop for i below r do (setf (aref v i) (floor n (+ i 1))))
      (loop for i from r for j downfrom (- (aref v (- r 1)) 1) above 0
         do (setf (aref v i) j))
      (loop for i below size
         do (setf (aref s i) (- (floor (* (aref v i) (+ (aref v i) 1)) 2) 1)))
      (loop for p from 2 to r
         if (> (aref s (- size p)) (aref s (- size p -1)))
         do (let ((sp (aref s (- size p -1))) (p2 (* p p)))
              (declare (u64 sp p2))
              (loop for i below size
                 until (< (aref v i) p2)
                 do (decf (aref s i) (* p (- (aref s (check (floor (aref v i) p) n ndr size)) sp))))))
      (aref s 0))))

#+sbcl
(defun bc (str)
  (sb-ext:run-program
   "/bin/bash"
   (list "-c" (concatenate 'string "echo '" str "' | BC_LINE_LENGTH=0 bc -l"))
   :output *standard-output*))

(defun phi (n)
  (reduce '* (mapcar (lambda (i) (- 1 (/ i))) (factor n))
          :initial-value n))

(defun carmichael (n)
  (reduce #'lcm (mapcar #'(lambda (pair)
                            (* (1- (car pair))
                               (expt (car pair) (1- (cdr pair)))))
                        (factor2 n))))

(defun get-divisors (n)
  (let ((factors (factor2 n)))
    (labels ((g (ls)
               (if (null ls)
                   (list 1)
                   (mapcan #'(lambda (k) (loop for i to (second (first ls))
                                       for e = 1 then (* e (caar ls))
                                       collect (* e k)))
                           (g (cdr ls))))))
      (sort (g factors) '<))))

(defun count-d (n &aux (prod 1) (limit (isqrt n)))
  (declare (optimize (speed 3) (debug 0) (safety 0))
           (fixnum n prod limit))
  (assert (> n 0))
  (loop for i fixnum = 2 then (if (= i 2) 3 (+ i 2))
     if (and (> i limit) (> n 1))
     do (setf prod (* prod 2)) and do (setf n 1)
     if (= n 1) return prod
     if (zerop (mod n i))
     do (loop for k fixnum from 1 do (setf n (/ n i))
           while (zerop (mod n i))
           finally (setf prod (* prod (1+ k))))
       (setf limit (isqrt n))))

(defun sum-divisors (n &aux (limit (isqrt n)))
  (loop for i from 1 to limit
     for (q r) = (multiple-value-list (floor n i))
     if (zerop r) sum (+ i q) into s
     finally (return (if (= (* limit limit) n) (- s limit) s))))

;; often faster
(defun sum-divisors2 (n)
  (loop with prod = 1
     for (p . k) in (factor2 n)
     do (setf prod (* prod (1- (expt p (1+ k))) (/ (1- p))))
     finally (return prod)))

(defun make-primes (limit)
  (declare (fixnum limit))
  (let ((vec (make-array (ceiling (* 1.23d0 (/ limit (log limit))))
                         :fill-pointer 0
                         :element-type '(unsigned-byte 32))))
    (if (< limit 2) #()
        (loop with len = (- (ash limit -1) 1)
           with sieve = (make-array (1+ len) :element-type 'bit)
           for i fixnum below (floor (isqrt limit) 2)
           if (zerop (bit sieve i))
           do (loop for j fixnum from (+ 3 (* (ash i 1) (+ 3 i)))
                 below len by (+ 3 (ash i 1))
                 do (setf (bit sieve j) 1))
           finally (vector-push 2 vec)
             (loop for i fixnum below len
                if (zerop (bit sieve i))
                do (vector-push (+ 3 (ash i 1)) vec))
             (return vec)))))

(defun make-n-primes (n)
  (loop with c = 0
     for i from 2
     if (primep i) collect i and do (incf c)
     while (< c n)))

(defun binary-search (array low high target)
  (if (> low high) nil
      (let ((mid (floor (+ low high) 2)))
        (declare (fixnum mid))
        (cond ((= target (aref array mid)) mid)
              ((< target (aref array mid))
               (binary-search array low (1- mid) target))
              (t
               (binary-search array (1+ mid) high target))))))

(defun bs (array low high target)
  (let ((mid (floor (+ low high) 2)))
    (declare (fixnum mid))
    (cond ((and (<= (aref array mid) target) (< target (aref array (+ 1 mid)))) mid)
          ((< target (aref array mid)) (bs array low mid target))
          (t (bs array mid high target)))))

(defmacro do-combinations ((var lists) &body body)
  ;; (do-combinations (n ((1 2 3) (10 20 30)))
  ;; (print n))
  (let* ((lst (mapcar #'(lambda (x)
                          `(loop for ,(gensym) in (list ,@x) do))
                      lists))
         (symbols (mapcar #'third lst)))
    (reduce #'(lambda (x y) `(,@y ,x))
            lst
            :initial-value `(let ((,var (list ,@symbols)))
                              ,@body))))

(defun split (str)
  (loop for start = 0 then (1+ end)
     for end = (position #\  str :start start)
     collect (subseq str start end)
     while end))

(defun read-string ()
  (with-output-to-string (str)
    (loop for c = (read-char t nil nil)
       while (digit-char-p c)
       do (princ c str))))

;; matrix
(defun mul (ma mb mod)
  (let* ((size (array-dimension ma 0))
         (mc (make-array (list size size))))
    (loop for i below size do
         (loop for j below size do
              (loop with sum = 0
                 for k below size
                 do (setf sum (mod (+ sum (* (aref ma i k) (aref mb k j))) mod))
                 finally (setf (aref mc i j) sum))))
    mc))

(defun mexp-mod (m e mod)
  (let* ((size (array-dimension m 0))
         (result (make-array (list size size))))
    (loop for i below size do (setf (aref result i i) 1))
    (loop if (zerop e) return result
       if (oddp e) do (setf result (mul result m mod))
       do (setf e (ash e -1)
                m (mul m m mod)))))
