(declaim (inline squarep))
(defun squarep (n)
  (let ((sqrt (isqrt n)))
    (and (= (* sqrt sqrt) n) sqrt)))

(defun factorial (n &aux (p 1))
  (loop for i from 2 to n
     do (setf p (* p i))
     finally (return p)))

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

(defun c (n r &aux (prod 1))
  (setf r (min r (- n r)))
  (loop for n1 from n downto (- n r -1)
     for r1 from r downto 1
     do (setf prod (* prod (/ n1 r1)))
     finally (return prod)))

(defun parse (n &aux result)
  (loop
     (if (zerop n) (return (or result (list 0))))
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

(defun factor (n)
  (mapcar #'car (factor2 n)))

(defun factor2 (n)
  (declare (fixnum n))
  (append
   (loop with limit fixnum = (isqrt n)
      for i fixnum in '(2 3 5)
      if (and (> i limit) (> n 1)) collect (cons n 1) and do (setf n 1)
      until (= n 1)
      if (zerop (mod n i))
      collect (cons i (loop for c fixnum from 1 do (setf n (/ n i))
                         unless (zerop (mod n i)) return c))
      and do (setf limit (isqrt n)))
   (loop with limit fixnum = (isqrt n)
      with i fixnum = 7
      with list = '#1=(4 2 4 2 4 6 2 6 . #1#)
      for k fixnum in list
      if (and (> i limit) (> n 1)) collect (cons n 1) and do (setf n 1)
      until (= n 1)
      do (incf i k)
      if (zerop (mod n i))
      collect (cons i (loop for c fixnum from 1 do (setf n (/ n i))
                         unless (zerop (mod n i)) return c))
      and do (setf limit (isqrt n)))))

#+sbcl
(defun factor3 (n)
  (with-input-from-string
      (in (with-output-to-string (out)
            (sb-ext:run-program "/usr/bin/factor" (list (write-to-string n)) :output out)))
    (loop (if (char= #\: (read-char in)) (return)))
    (loop for n = (read in nil nil)
       while n collect n)))

(defun phi (n)
  (reduce '* (mapcar (lambda (i) (- 1 (/ i))) (factor n))
          :initial-value n))

(defun make-primes (maximum)
  (sieve-of-eratosthenes maximum))

(defun count-d (n)
  (declare (optimize (speed 3) (debug 0) (safety 0))
           (fixnum n))
  (let ((prod 1) (limit (isqrt n)))
    (declare (fixnum prod))
    (loop for i fixnum = 2 then (if (= i 2) 3 (+ i 2))
       if (and (> i limit) (> n 1))
       do (setf prod (* prod 2)) and do (setf n 1)
       if (= n 1) return prod
       if (zerop (mod n i))
       do (loop for k fixnum from 1 do (setf n (/ n i))
             while (zerop (mod n i))
             finally (setf prod (* prod (1+ k))))
         (setf limit (isqrt n)))))

(defun sum-divisors (n)
  (loop with limit = (isqrt n)
     for i from 1 to limit
     for (q r) = (multiple-value-list (floor n i))
     if (zerop r) sum (+ i q) into s
     finally (return (if (= (* limit limit) n) (- s limit) s))))

(defun sieve-of-eratosthenes (maximum)
  (declare (optimize (speed 3) (debug 0) (safety 0))
           (fixnum maximum))
  (cond ((< maximum 2) nil)
        ((= maximum 2) (list 2))
        ((< maximum 5) (list 2 3))
        (t (loop with candidate fixnum = 7
              with sieve = (make-array (1+ maximum)
                                       :element-type 'bit
                                       :initial-element 0)
              with list = '#1=(4 2 4 2 4 6 2 6 . #1#)
              for k fixnum in list
              if (> candidate maximum) return (list* 2 3 5 values)
              if (zerop (bit sieve candidate))
              collect candidate into values
              and do (loop for composite fixnum from (the fixnum (expt candidate 2))
                        to maximum by candidate
                        do (setf (bit sieve composite) 1))
              do (incf candidate k)))))

(defun primes (limit)
  (declare (optimize (speed 3) (debug 0) (safety 0))
           (fixnum limit))
  (if (< limit 2) nil
      (loop with len = (+ (floor limit 2) (mod limit 2) -1)
         with sieve = (make-array (1+ len)
                                  :element-type 'bit
                                  :initial-element 1)
         for i fixnum below (floor (floor (sqrt limit)) 2)
         unless (zerop (bit sieve i))
         do (loop for j fixnum from (+ 3 (* (ash i 1) (+ 3 i)))
               below len by (+ 3 (ash i 1))
               do (setf (bit sieve j) 0))
         finally (return
                   (cons 2
                         (loop for i fixnum below len
                            unless (zerop (bit sieve i))
                            collect (+ 3 (ash i 1))))))))
