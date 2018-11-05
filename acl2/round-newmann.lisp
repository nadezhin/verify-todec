(in-package "RTL")
(include-book "section3")
(include-book "alpha-separated")

(local (include-book "rtl/rel11/support/basic" :dir :system))
(local (acl2::allow-arith5-help))

(define round-Newmann
  ((x real/rationalp))
  :returns (vn integerp :rule-classes ())
  (acl2::b*
   ((x (realfix x)))
   (if (integerp x)
       (* 2 x)
     (1+ (* 2 (floor x 1)))))
  ///
  (fty::deffixequiv round-Newmann)
  (defrule round-Newmann-when-integerp
    (implies (integerp (realfix x))
             (equal (round-Newmann x) (* 2 (realfix x)))))
#|
  (acl2::with-arith5-help
   (defruled round-Newmann-when-not-integerp
     (implies
      (not (integerp (realfix x)))
      (and (< (* 2 (floor x 1)) (round-Newmann x))
           (< (round-Newmann x) (+ 2 (* 2 (floor x 1))))))
     :rule-classes ((:linear :trigger-terms ((round-Newmann x))))
     :disable ACL2::|(* 2 (floor x y))|))
|#
  (acl2::with-arith5-help
   (defrule signum-round-Newmann
     (implies (integerp m)
              (equal (signum (- (round-Newmann x) (* 2 m)))
                     (signum (- (realfix x) m))))
     :cases ((<= m (floor x 1))
             (>= m (1+ (floor x 1))))
     :enable round-Newmann
     :disable ACL2::|(* 2 (floor x y))|)))

(acl2::with-arith5-help
 (defrule round-Newmann-when-between-integers
  (implies
   (and (integerp m)
        (< m (realfix x))
        (< (realfix x) (1+ m)))
   (equal (round-Newmann x) (1+ (* 2 m))))
  :rule-classes ()
  :use (signum-round-Newmann
        (:instance signum-round-Newmann
                   (m (1+ m))))))

(define round-Newmann-approx
  ((approx real/rationalp)
   (threshold real/rationalp))
  :returns (vn integerp :rule-classes ())
  (acl2::b*
   ((approx (realfix approx))
    (threshold (realfix threshold)))
   (+ (* 2 (floor approx 1))
      (if (<= threshold (mod approx 1)) 1 0)))
  ///
  (fty::deffixequiv round-Newmann-approx)
  (acl2::with-arith5-nonlinear-help
   (defrule round-Newmann-approx-correct-n
    (acl2::b*
     ((alpha*x (* alpha x))
      (err (- approx alpha*x)))
     (implies
      (and (alpha-separated alpha maximum a b)
           (real/rationalp alpha)
           (natp x)
           (real/rationalp approx)
           (real/rationalp threshold)
           (<= x maximum)
           (<= 0 err)
           (< err b)
           (<= 0 a)
           (< err threshold)
           (<= threshold a)
           (posp n))
      (equal (round-Newmann-approx (/ approx n) (/ threshold n))
             (round-Newmann (/ alpha*x n)))))
    :enable round-Newmann-approx
    :disable acl2::|(* 2 (floor x y))|
    :cases ((< (* alpha x (/ n)) (floor approx n))
            (= (* alpha x (/ n)) (floor approx n))
            (and (< (floor approx n) (* alpha x (/ n)))
                 (< (* alpha x (/ n)) (1+ (floor approx n))))
            (<= (1+ (floor approx n)) (* alpha x (/ n))))
    :hints
    (("subgoal 4" :use
      (:instance alpha-separated-necc
                 (y (* n (floor approx n)))))
     ("subgoal 2" :use
      ((:instance round-Newmann-when-between-integers
                  (x (* alpha x (/ n)))
                  (m (floor approx n)))
       (:instance alpha-separated-necc
                  (y (* n (floor approx n))))))))))

(defrule round-Newmann-approx-correct
  (acl2::b*
   ((alpha*x (* alpha x))
    (err (- approx alpha*x)))
   (implies
    (and (alpha-separated alpha maximum a b)
         (real/rationalp alpha)
         (natp x)
         (real/rationalp approx)
         (real/rationalp threshold)
         (<= x maximum)
         (<= 0 err)
         (< err b)
         (<= 0 a)
         (< err threshold)
         (<= threshold a))
    (equal (round-Newmann-approx approx threshold)
           (round-Newmann alpha*x))))
  :use (:instance  round-Newmann-approx-correct-n
                   (n 1)))

#|
alpha = 2^ord2alpha * 0.mant + eps

x0 63:0
x1 126:64
y0 126:63
y1 189:127
z 126:63
p0 62:0
p1 125:63
p2 188:126

vn [:(126-ord2alpha)]*2 + sticky
|#
