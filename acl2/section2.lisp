(in-package "RTL")
(include-book "section1")

(local (include-book "rtl/rel11/support/bits" :dir :system))
(local (include-book "rtl/rel11/support/float" :dir :system))
(local (acl2::allow-arith5-help))

; Section 2 of the paper

(defconst *roundTiedToEven* 'rne)

(define recover
  ((d integerp)
   (i integerp)
   (f formatp))
  :returns (v rationalp :rule-classes :type-prescription)
  (acl2::b*
   ((d (ifix d))
    (i (ifix i))
    (f (format-fix f))
    (dv (* d (expt (D) i))))
   (if (<= (spn f) (abs dv))
       (rnd dv *roundTiedToEven* (prec f))
     (drnd dv *roundTiedToEven* f)))
  ///
  (fty::deffixequiv recover))

(define D-length
  ((d integerp))
  :returns (D-length natp :rule-classes :type-prescription
                     :hints (("goal" :in-theory (enable (D))
                              :use (:instance expe-monotone
                                             (b (D))
                                             (x 1)
                                             (y d)))))
  (if (zip d)
      0
    (+ 1 (expe d (D))))
  ///
  (fty::deffixequiv D-length)
  (defrule D-length-type-when-nonzero
    (implies (not (zip d))
             (posp (D-length d)))
    :rule-classes :type-prescription
    :in-theory (enable (D))
    :use (:instance expe-monotone
                    (b (D))
                    (x 1)
                    (y d))))

(define D-value
  ((d integerp)
   (i integerp))
  :returns (value rationalp :rule-classes :type-prescription)
  (* (ifix d) (expt 2 i))
  ///
  (fty::deffixequiv D-value))

(define D-even
  ((d integerp))
  :returns (yes booleanp :rule-classes ())
  (evenp (digitn (abs (ifix d)) 0 (D)))
  ///
  (fty::deffixequiv D-even)
  (acl2::with-arith5-help
  (defruled D-even-as-eveno
    (equal (D-even d)
           (evenp (ifix d)))
    :enable (digitn-rec-0 (D)))))

(define better
  ((d1 integerp)
   (i1 integerp)
   (d2 integerp)
   (i2 integerp)
   (v real/rationalp))
  :returns (better booleanp :rule-classes ())
  (acl2::b*
   ((v (realfix v)))
   (or (< (D-length d1)
          (D-length d2))
       (and (= (D-length d1)
               (D-length d2))
            (< (abs (- (D-value d1 i1) v))
               (abs (- (D-value d2 i2) v))))
       (and (= (D-length d1)
               (D-length d2))
            (= (abs (- (D-value d1 i1) v))
               (abs (- (D-value d2 i2) v)))
            (D-even d1)
            (not (D-even d2)))))
  ///
  (fty::deffixequiv better :hints (("goal" :in-theory (disable ifix)))))

(defun-sk exists-better (d* i* f)
  (declare (xargs :guard (and (integerp d*)
                              (integerp i*)
                              (formatp f))))
  (exists (d? i?)
          (let ((v (recover d* i* f)))
            (and (integerp d?)
                 (integerp i?)
                 (= (recover d? i? f) v)
                 (better d? i? d* i* v)))))

(define specification
  ((d integerp)
   (i integerp)
   (f formatp)
   (v real/rationalp))
  (and (= (recover d i f) (realfix v))
       (not (exists-better (ifix d) (ifix i) (format-fix f))))
  ///
  (fty::deffixequiv specification :hints (("goal" :in-theory (disable ifix)))))

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
