(in-package "RTL")
(include-book "section1")

(local (include-book "rtl/rel11/support/float" :dir :system))
(local (acl2::allow-arith5-help))

; Section 2 of the paper

(define recover-p
  ((d_ integerp)
   (i integerp)
   (v real/rationalp)
   (f formatp))
  :guard (or (nrepp v f) (drepp v f))
  :returns (yes booleanp :rule-classes ())
  (acl2::b*
   ((d_ (ifix d_))
    (i (ifix i))
    (v (realfix v))
    (f (format-fix f))
    (dv (* d_ (expt (D) i))))
   (or (and (nrepp v f) (equal v (rnd dv 'rne (prec f))))
       (and (drepp v f) (equal v (drnd dv 'rne f)))))
  ///
  (fty::deffixequiv recover-p))

(defun-sk best-recover (d* i* v f)
  (declare (xargs :guard (and (integerp d*)
                              (integerp i*)
                              (real/rationalp v)
                              (formatp f)
                              (or (nrepp v f) (drepp v f)))))
  (forall (d? i?)
          (or (not (integerp d?))
              (not (integerp i?))
              (not (recover-p d? i? v f))
              (and (equal d? d*) (equal i? i*))
              (< i? i*)
              (and (equal i? i*)
                   (< (abs (- (* d? (expt (D) i?)) v))
                      (abs (- (* d* (expt (D) i*)) v))))
              (and (equal i? i*)
                   (= (abs (- (* d? (expt (D) i?)) v))
                      (abs (- (* d* (expt (D) i*)) v)))
                   (oddp d?)))))


(define ord2
  ((x pos-rationalp))
  :returns (ord2 integerp :rule-classes ())
  (let ((x (pos-rational-fix x)))
    (1+ (expe x 2)))
  ///
  (fty::deffixequiv ord2))

(define ordD
  ((x pos-rationalp))
  :returns (ordD integerp :rule-classes ())
  (let ((x (pos-rational-fix x)))
    (1+ (expe x (D))))
  ///
  (fty::deffixequiv ordD))

(acl2::with-arith5-help
 (defrule result-1-1
   (implies (and (real/rationalp x)
                 (integerp m)
                 (integerp n))
            (equal (and (<= m x) (< x n))
                   (and (<= m (fl x)) (< (fl x) n))))
   :rule-classes ()))

(defrule result-1-2
  (implies (and (real/rationalp x)
                (integerp m)
                (integerp n))
           (equal (and (< m x) (<= x n))
                  (and (< m (cg x)) (<= (cg x) n))))
  :rule-classes ())

(defrule result-1-3
  (equal (= k (ordD x))
         (let ((x (pos-rational-fix x)))
           (and (integerp k)
                (<= (expt (D) (- k 1)) x)
                (< x (expt (D) k)))))
  :rule-classes ()
  :enable (ordD expe-lower-bound expe-upper-bound)
  :cases ((= k (ordD x)))
  :use (:instance expe-unique
                  (b (D))
                  (x (pos-rational-fix x))
                  (n (1- k))))

(defrule result-1-3-ord2
  (equal (= k (ord2 x))
         (let ((x (pos-rational-fix x)))
           (and (integerp k)
                (<= (expt 2 (- k 1)) x)
                (< x (expt 2 k)))))
  :rule-classes ()
  :enable (ord2 expe-lower-bound expe-upper-bound)
  :cases ((= k (ord2 x)))
  :use (:instance expe-unique
                  (b 2)
                  (x (pos-rational-fix x))
                  (n (1- k))))

(defrule ordD-1
  (equal (ordD 1) 1)
  :use (:instance result-1-3 (x 1) (k 1)))

(acl2::with-arith5-help
 (defrule ordD-expt-D
   (implies (integerp k)
            (equal (ordD (expt (D) k)) (+ k 1)))
   :use (:instance result-1-3 (x (expt (D) k)) (k (+ k 1)))))

(defrule ordD-D
  (equal (ordD (D)) 2)
  :expand (expt (D) 1)
  :use (:instance ordD-expt-D (k 1)))

(defrule ordD-/D
  (equal (ordD (/ (D))) 0)
  :use (:instance ordD-expt-D (k -1)))

(defruled result-1-4
  (implies (< (pos-rational-fix x)
              (pos-rational-fix y))
           (<= (ordD x)
               (ordD y)))
  :enable ordD
  :use (:instance expe-monotone
                  (b (D))
                  (x (pos-rational-fix x))
                  (y (pos-rational-fix y))))

(acl2::with-arith5-help
 (defruled result-1-5
   (implies (and (pos-rationalp d)
                 (integerp r))
            (equal (ordD (* d (expt (D) r)))
                   (+ r (ordD d))))
   :enable ordD
   :use (:instance expe-shift (b (D)) (x d) (n r))))

(acl2::with-arith5-help
 (defruled result-1-6
  (implies (and (rationalp x)
                (<= 1 x))
           (equal (ordD (fl x)) (ordD x)))
  :enable (ordD pos-rationalp)
  :use ((:instance expe-unique (b (D)) (n (expe (fl x) (D))))
        (:instance expe-lower-bound (b (D)) (x (fl x)))
        (:instance expe-upper-bound (b (D)) (x (fl x)))
        (:instance result-1-1
                   (m (expt (D) (expe (fl x) (D))))
                   (n (expt (D) (1+ (expe (fl x) (D)))))))))
