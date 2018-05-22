(in-package "RTL")
(include-book "section3")

(local (acl2::allow-arith5-help))

(acl2::with-arith5-help
(define vl
  ((v pos-rationalp)
   (f formatp))
  :returns (vl rationalp :rule-classes :type-prescription)
  (let* ((v (pos-rational-fix v))
         (q (q v f))
         (c (c v f)))
    (if (or (> c (2^{P-1} f))
            (= q (Qmin f)))
        (* (- c 1/2) (expt 2 q))
      (* (- c 1/4) (expt 2 q))))
  ///
  (fty::deffixequiv vl)
  (acl2::with-arith5-help
   (defrule vl-linear
     (< (vl v f) (pos-rational-fix v))
     :rule-classes :linear
     :enable c))))

(define vr
  ((v pos-rationalp)
   (f formatp))
  :returns (vl rationalp :rule-classes :type-prescription)
  (let* ((v (pos-rational-fix v))
         (q (q v f))
         (c (c v f)))
    (* (+ c 1/2) (expt 2 q)))
  ///
  (fty::deffixequiv vr)
  (acl2::with-arith5-help
   (defrule vr-linear
     (> (vr v f) (pos-rational-fix v))
     :rule-classes :linear
     :enable c)))

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
    :rule-classes ()))

(defrule v-in-Rv
  (implies (pos-rationalp v)
           (in-tau-intervalp v (Rv v f)))
  :use fix-v-in-Rv)
