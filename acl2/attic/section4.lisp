(in-package "RTL")
(include-book "section3")

(local (include-book "rtl/rel11/support/float" :dir :system))
(local (acl2::allow-arith5-help))

(define vl
  ((v pos-rationalp)
   (f formatp))
  :returns (vl rationalp :rule-classes ())
  (let* ((q (q v f))
         (c (c v f)))
    (if (or (> c (2^{P-1} f))
            (= q (Qmin f)))
        (* (- c 1/2) (expt 2 q))
      (* (- c 1/4) (expt 2 q))))
  ///
  (fty::deffixequiv vl)
  (defruled vl-alt
    (equal (vl v f)
           (let* ((q (q v f))
                  (c (c v f)))
             (if (or (not (= c (2^{P-1} f)))
                     (= q (Qmin f)))
                 (* (- c 1/2) (expt 2 q))
               (* (- c 1/4) (expt 2 q)))))
    :rule-classes :definition
    :enable c-as-sigc
    :cases ((<= (Qmin f) (expq (pos-rational-fix v) (P f) 2)))
    :hints (("subgoal 2" :in-theory (enable q))
            ("subgoal 1" :in-theory (enable sigc-lower-bound 2^{P-1}))))
  (acl2::with-arith5-help
   (defrule vl-linear
     (< (vl v f) (pos-rational-fix v))
     :rule-classes :linear
     :enable c)))

(acl2::with-arith5-help
 (define vr
  ((v pos-rationalp)
   (f formatp))
  :returns (vl pos-rationalp :rule-classes ())
  (let* ((q (q v f))
         (c (c v f)))
    (* (+ c 1/2) (expt 2 q)))
  ///
  (fty::deffixequiv vr)
  (acl2::with-arith5-help
   (defrule vr-linear
     (> (vr v f) (pos-rational-fix v))
     :rule-classes :linear
     :enable c))))

(define Rv
  ((v pos-rationalp)
   (f formatp))
  :returns (intvl tau-intervalp)
  (let* ((open (not (integerp (* 1/2 (c v f))))))
    (make-tau-interval
     'rationalp open (vl v f) open (vr v f)))
  ///
  (fty::deffixequiv Rv
                    :hints (("goal" :in-theory (disable pos-rational-fix))))
  (defrule fix-v-in-Rv
    (in-tau-intervalp (pos-rational-fix v) (Rv v f))
    :rule-classes ())
  (defrule tau-interval-lo-Rv-type
    (rationalp (tau-interval-lo (Rv v f)))
    :rule-classes :type-prescription
    :enable tau-interval-lo)
  (defrule tau-interval-hi-Rv-type
    (rationalp (tau-interval-hi (Rv v f)))
    :rule-classes :type-prescription
    :enable tau-interval-hi)
  (defruled in-tau-intervalp-Rv
    (equal (in-tau-intervalp x (Rv v f))
           (and (rationalp x)
                (if (integerp (* 1/2 (c v f)))
                    (and (<= (vl v f) x) (<= x (vr v f)))
                  (and (< (vl v f) x) (< x (vr v f))))))))

(define wid-Rv
  ((v pos-rationalp)
   (f formatp))
  :returns (wid pos-rationalp :rule-classes :type-prescription
                :hints (("goal" :in-theory (enable Rv pos-rationalp))))
  (- (tau-interval-hi (Rv v f)) (tau-interval-lo (Rv v f)))
  :guard-hints (("goal" :in-theory (enable Rv)))
  ///
  (fty::deffixequiv wid-Rv)
  (defruled wid-Rv-as-c-q
    (let ((q (q v f))
          (c (c v f)))
      (equal (wid-Rv v f)
             (* (if (or (not (= c (2^{P-1} f))) (= q (Qmin f))) 1 3/4)
                (expt 2 q))))
    :enable (Rv vl-alt vr)))

(acl2::with-arith5-help
 (defruled wid-Rv>=MIN_VALUE
   (<= (MIN_VALUE f) (wid-Rv v f))
   :rule-classes :linear
   :enable (wid-Rv-as-c-q MIN_VALUE)))

(acl2::with-arith5-help
 (defruled wid-Rv<=max-ulp-when-finite-positive-binary
   (implies (finite-positive-binary-p v f)
            (<= (wid-Rv v f) (expt 2 (Qmax f))))
   :rule-classes :linear
   :enable (wid-Rv-as-c-q)))

(defrule v-in-Rv
  (implies (pos-rationalp v)
           (in-tau-intervalp v (Rv v f)))
  :use fix-v-in-Rv)

(defrule u-or-w-in-Rv
   (let ((v (pos-rational-fix v)))
     (implies (and (<= u v)
                   (< v w)
                   (< (- w u) (wid-Rv v f))
                   (rationalp u)
                   (rationalp w))
              (or (in-tau-intervalp u (Rv v f))
                  (in-tau-intervalp w (Rv v f)))))
   :rule-classes ()
   :enable (wid-Rv Rv))

(defrule at-most-one-in-Rv
   (let ((v (pos-rational-fix v)))
     (implies (and (> (- w u) (wid-Rv v f))
                   (rationalp u)
                   (rationalp w))
              (or (not (in-tau-intervalp u (Rv v f)))
                  (not (in-tau-intervalp w (Rv v f))))))
   :rule-classes ()
   :enable (wid-Rv Rv))

(in-theory (disable tau-intervalp in-tau-intervalp tau-interval-lo tau-interval-hi))
