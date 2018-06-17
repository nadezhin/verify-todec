(in-package "RTL")
(include-book "section4")

(local (include-book "rtl/rel11/support/float" :dir :system))
(local (acl2::allow-arith5-help))

(define e
  ((x pos-rationalp))
  :returns (e integerp :rule-classes ())
  (ordD x)
  ///
  (fty::deffixequiv e)
  (defruled e-as-expe
    (equal (e x)
           (+ (expe (pos-rational-fix x) (D)) 1))
    :enable ordD))

(acl2::with-arith5-help
 (define f
   ((x pos-rationalp))
   :returns (f pos-rationalp :rule-classes ())
   (* (pos-rational-fix x) (expt (D) (- (e x))))
   ///
   (fty::deffixequiv f)
   (defruled f-as-sigm
     (equal (f x)
            (let ((x (pos-rational-fix x)))
              (/ (sigm x (D)) (D))))
     :enable (sigm e-as-expe))))

(acl2::with-arith5-nonlinear-help
 (defrule f-linear
   (and (<= (/ (D)) (f x))
        (< (f x) 1))
   :rule-classes :linear
   :enable f-as-sigm
   :use ((:instance sigm-lower-bound
                    (b (D))
                    (x (pos-rational-fix x)))
         (:instance sigm-upper-bound
                    (b (D))
                    (x (pos-rational-fix x))))))

(defrule ordD-f
  (equal (ordD (f x)) 0)
  :use (:instance result-1-3 (k 0) (x (f x))))

(define Emin
  ((f formatp))
  :returns (Emin integerp :rule-classes ())
  (e (MIN_VALUE f))
  ///
  (fty::deffixequiv Emin))

(define Esmall
  ((f formatp))
  :returns (Esmall integerp :rule-classes ())
  (e (MIN_NORMAL f))
  ///
  (fty::deffixequiv Esmall))

(define Emax
  ((f formatp))
  :returns (Emax integerp :rule-classes ())
  (e (MAX_VALUE f))
  ///
  (fty::deffixequiv Emax))

(defruled e-range-when-finite-positive-binary
  (implies (finite-positive-binary-p (pos-rational-fix v) f)
           (and (<= (Emin f) (e v))
                (<= (e v) (Emax f))))
  :rule-classes ((:linear :trigger-terms ((e v))))
  :enable (e Emin Emax)
  :use ((:instance result-1-4
                   (x (MIN_VALUE f))
                   (y (pos-rational-fix v)))
        (:instance result-1-4
                   (x (pos-rational-fix v))
                   (y (MAX_VALUE f)))
        (:instance finite-positive-binary-range
                   (v (pos-rational-fix v)))))

; Use result-2 statement as definition in proof script
(define has-D-length
  ((x pos-rationalp)
   (i posp))
  :returns (yes booleanp :rule-classes ())
  (let ((x (pos-rational-fix x))
        (i (acl2::pos-fix i)))
    (integerp (* (f x) (expt (D) i))))
  ///
  (fty::deffixequiv has-D-length)
  (acl2::with-arith5-help
   (defruled has-D-length-as-exactrp
     (equal (has-D-length x i)
            (exactrp (pos-rational-fix x) (acl2::pos-fix i) (D)))
     :enable (f-as-sigm exactrp sigc)))
  (acl2::with-arith5-help
   (defruled has-D-length-necc ; part of result-2
     (implies (has-D-length x i)
              (let* ((x (pos-rational-fix x))
                     (i (acl2::pos-fix i))
                     (r (- (e x) i))
                     (d (* x (expt (D) (- r)))))
                (and (integerp r)
                     (integerp d)
                     (equal (ordD d) i))))
     :enable (result-1-5 e f)))
  (acl2::with-arith5-help
   (defrule has-D-length-suff ; part of result-2
     (implies (and (integerp r)
                   (posp d))
              (let ((x (* d (expt (D) r)))
                    (i (ordD d)))
                (has-D-length x i)))
     :enable (f e result-1-5)
     :use ((:instance result-1-4 (x 1) (y d))
           (:instance result-1-3 (x 1) (k 1))))))

(defruled has-D-length-monotone
  (implies (and (has-D-length x i)
                (<= (acl2::pos-fix i) (acl2::pos-fix j)))
           (has-D-length x j))
  :enable (has-D-length-as-exactrp exactrp-<=))
