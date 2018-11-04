(in-package "RTL")
(include-book "section3")
(include-book "alpha-separated")

(local (include-book "rtl/rel11/support/basic" :dir :system))
(local (acl2::allow-arith5-help))

(define round-Newmann
  ((x real/rationalp))
  :returns (vn integerp)
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
  (acl2::with-arith5-help
   (defruled round-Newmann-when-not-integerp
     (implies
      (not (integerp (realfix x)))
      (and (< (* 2 (floor x 1)) (round-Newmann x))
           (< (round-Newmann x) (+ 2 (* 2 (floor x 1))))))
     :rule-classes ((:linear :trigger-terms ((round-Newmann x))))
     :disable ACL2::|(* 2 (floor x y))|))
  (acl2::with-arith5-help
   (defrule signum-round-Newmann
     (implies (integerp m)
              (equal (signum (- (round-Newmann x) (* 2 m)))
                     (signum (- (realfix x) m))))
     :cases ((<= m (floor x 1))
             (>= m (1+ (floor x 1))))
     :enable round-Newmann
     :disable ACL2::|(* 2 (floor x y))|)))
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
