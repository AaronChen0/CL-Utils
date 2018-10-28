(declaim (inline squarep))
(defun squarep (n)
  (let ((sqrt (isqrt n)))
    (and (= (* sqrt sqrt) n) sqrt)))

(defun factorial (n)
  (loop with product = 1
     for i from 2 to n
     do (setf product (* product i))
     finally (return product)))

(defun fib (n)
  (loop with (a b p q) = (list 1 0 0 1)
     until (zerop n)
     if (oddp n) do (psetf a (+ (* b q) (* a (+ p q)))
                           b (+ (* b p) (* a q)))
     do (psetf p (+ (* p p) (* q q))
               q (* q (+ q (* 2 p)))
               n (ash n -1))
     finally (return b)))

(defun exp-mod (b e m)
  (setf b (mod b m))
  (loop with p = 1 until (zerop e)
     if (oddp e) do (setf p (mod (* p b) m))
     do (setf e (ash e -1) b (mod (* b b) m))
     finally (return p)))

(defun c (n r)
  (setf r (min r (- n r)))
  (loop with prod = 1
     for n1 from n downto (- n r -1)
     for r1 from r downto 1
     do (setf prod (* prod (/ n1 r1)))
     finally (return prod)))

(defun parse (n)
  (loop with result
     initially (if (zerop n) (return (list 0)))
     until (zerop n) do
       (multiple-value-bind (quotient remainder) (floor n 10)
         (push remainder result)
         (setf n quotient))
     finally (return result)))

(defun primep (n)
  (or (= n 2) (= n 3) (= n 5)
      (and (> n 1)
           (oddp n)
           (not (zerop (mod n 3)))
           (not (zerop (mod n 5)))
           (loop with k = 7
              with list = '#1=(4 2 4 2 4 6 2 6 . #1#)
              for i in list
              until (> (* k k) n)
              if (zerop (mod n k)) return nil
              do (incf k i)
              finally (return t)))))

(defun factor (n)
  (mapcar #'car (factor2 n)))

(defun factor2 (n)
  (declare (fixnum n))
  (append
   (loop with limit of-type fixnum = (isqrt n)
      for i fixnum in '(2 3 5)
      if (and (> i limit) (> n 1)) collect (cons n 1) and do (setf n 1)
      until (= n 1)
      if (zerop (mod n i))
      collect (cons i (loop for c fixnum from 1 do (setf n (/ n i))
                         while (zerop (mod n i))
                         finally (return c)))
      and do (setf limit (isqrt n)))
   (loop with limit of-type fixnum = (isqrt n)
      with i of-type fixnum = 7
      with list = '#1=(4 2 4 2 4 6 2 6 . #1#)
      for k of-type fixnum in list
      if (and (> i limit) (> n 1)) collect (cons n 1) and do (setf n 1)
      until (= n 1)
      do (incf i k)
      if (zerop (mod n i))
      collect (cons i (loop for c fixnum from 1 do (setf n (/ n i))
                         while (zerop (mod n i))
                         finally (return c)))
      and do (setf limit (isqrt n)))))

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
       until (= n 1)
       if (zerop (mod n i))
       do (loop for k fixnum from 1 do (setf n (/ n i))
             while (zerop (mod n i))
             finally (setf prod (* prod (1+ k))))
         (setf limit (isqrt n))
       finally (return prod))))

(defun sum-divisors (n)
  (loop with limit = (isqrt n)
     for i from 1 to limit
     for (q r) = (multiple-value-list (floor n i))
     if (zerop r) sum (+ i r) into s
     finally (return (if (= (* limit limit) n) (- s limit) s))))

(defun sieve-of-eratosthenes (maximum)
  (declare (optimize (speed 3) (debug 0) (safety 0))
           (fixnum maximum))
  (cond ((< maximum 2) nil)
        ((= maximum 2) (list 2))
        ((< maximum 5) (list 2 3))
        (t (loop
              with sieve = (make-array (1+ maximum)
                                       :element-type 'bit
                                       :initial-element 0)
              with list = '#1=(4 2 4 2 4 6 2 6 . #1#)
              with candidate of-type fixnum = 7
              for k fixnum in list
              until (> candidate maximum)
              when (zerop (bit sieve candidate))
              collect candidate into values
              and do (loop for composite fixnum from (the fixnum (expt candidate 2))
                        to maximum by candidate
                        do (setf (bit sieve composite) 1))
              do (incf candidate k)
              finally (return (list* 2 3 5 values))))))

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
