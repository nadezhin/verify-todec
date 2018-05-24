(in-package "RTL")
(include-book "section3")

(local (include-book "rtl/rel11/support/float" :dir :system))
(local (acl2::allow-arith5-help))

(define vl
  ((v pos-rationalp)
   (f formatp))
  :returns (vl rationalp :rule-classes :type-prescription)
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
    :hints (("subgoal 2" :in-theory (enable q-as-expq))
            ("subgoal 1" :in-theory (enable sigc-lower-bound 2^{P-1}))))
  (acl2::with-arith5-help
   (defrule vl-linear
     (< (vl v f) (pos-rational-fix v))
     :rule-classes :linear
     :enable c)))

(define vr
  ((v pos-rationalp)
   (f formatp))
  :returns (vl rationalp :rule-classes :type-prescription)
  (let* ((q (q v f))
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
    :rule-classes ())
  (acl2::with-arith5-help
   (defruled
     width-Rv
     (let ((q (q v f))
           (c (c v f))
           (Rv (Rv v f)))
       (equal (- (tau-interval-hi Rv) (tau-interval-lo Rv))
              (* (if (or (not (= c (2^{P-1} f))) (= q (Qmin f))) 1 3/4)
                 (expt 2 q))))
    :enable (vl-alt vr))))

(defrule v-in-Rv
  (implies (pos-rationalp v)
           (in-tau-intervalp v (Rv v f)))
  :use fix-v-in-Rv)

(defrule u-or-w-in-Rv
   (let* ((Rv (Rv v f))
         (wid (- (tau-interval-hi Rv) (tau-interval-lo Rv)))
         (v (pos-rational-fix v)))
     (implies (and (<= u v)
                   (< v w)
                   (< (- w u) wid)
                   (rationalp u)
                   (rationalp w))
              (or (in-tau-intervalp u (Rv v f))
                  (in-tau-intervalp w (Rv v f)))))
   :rule-classes ()
   :enable Rv)
