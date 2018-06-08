#|
(include-book "rtl/rel11/portcullis" :dir :system)
|#
(in-package "RTL")
(include-book "section10")

(local (include-book "rtl/rel11/support/float" :dir :system))
(local (include-book "std/basic/inductions" :dir :system))
(local (acl2::allow-arith5-help))

(acl2::with-arith5-help
 (define !s_i
  ((i posp)
   (v pos-rationalp)
   (f formatp))
  :returns (!s_i posp :rule-classes :type-prescription)
  (let ((i (min (H f) (acl2::pos-fix i))))
    (* (s_i i v) (expt (D) (- (H f) i))))
  ///
  (fty::deffixequiv !s_i)
  (acl2::with-arith5-nonlinear++-help
   (defruled !s_i-linear
     (let* ((!s_i (!s_i i v f))
            (H (H f)))
       (implies (and (posp i)
                     (<= i H))
                (and (<= (expt (D) (- H 1)) !s_i)
                     (< (- (* (f v) (expt (D) H)) (expt (D) (- H i)))
                        !s_i)
                     (<= !s_i (* (f v) (expt (D) H)))
                     (< !s_i (expt (D) H)))))
     :rule-classes ((:linear :trigger-terms ((!s_i i v f))))
     :use s_i-linear))
  (defrule ordD-!s_i
    (implies (and (posp i)
                  (<= i (H f)))
             (equal (ordD (!s_i i v f)) (H f)))
    :enable result-1-5)))

(acl2::with-arith5-help
 (define !t_i
  ((i posp)
   (v pos-rationalp)
   (f formatp))
  :returns (!t_i posp :rule-classes :type-prescription)
  (let ((i (min (H f) (acl2::pos-fix i))))
    (* (t_i i v) (expt (D) (- (H f) i))))
  ///
  (fty::deffixequiv !t_i)
  (acl2::with-arith5-nonlinear++-help
   (defruled !t_i-linear
     (let* ((!t_i (!t_i i v f))
            (H (H f)))
       (implies (and (posp i)
                     (<= i H))
                (and (< (expt (D) (- H 1)) !t_i)
                     (< (* (f v) (expt (D) H)) !t_i)
                     (<= !t_i (expt (D) H)))))
     :rule-classes ((:linear :trigger-terms ((!t_i i v f))))
     :use t_i-linear))
  (defrule ordD-!t_i
    (implies (and (posp i)
                  (<= i (H f))
                  (not (equal (!t_i i v f) (expt (D) (H f)))))
             (equal (ordD (!t_i i v f)) (H f)))
    :use ordD-t_i
    :enable result-1-5)))

(acl2::with-arith5-help
 (defruled !s_i-as-!s_H
   (let ((H (H f)))
     (implies (and (posp i)
                   (< i H))
              (equal (!s_i i v f)
                     (* (fl (/ (!s_i H v f) (expt (D) (- H i))))
                        (expt (D) (- H i))))))
   :enable (!s_i s_i)
   :use (:instance fl/int-rewrite
                   (x (* (f v) (expt (D) (H f))))
                   (n (expt (D) (- (H f) i))))))

(define !q
  ((x pos-rationalp)
   (f formatp))
  :returns (!q integerp :rule-classes ())
  (let ((q (q x f))
        (c (c x f)))
    (if (or (= q (Qmin f)) (not (= c (2^{P-1} f))))
        (- q 1)
      (- q 2)))
  ///
  (fty::deffixequiv !q))

(define !c
  ((x pos-rationalp)
   (f formatp))
  :returns (!c pos-rationalp :rule-classes ())
  (let ((q (q x f))
        (c (c x f)))
    (if (or (= q (Qmin f)) (not (= c (2^{P-1} f))))
        (* 2 c)
      (* 4 c)))
  ///
  (fty::deffixequiv !c)
  (defrule !c-linear
    (<= (!c x f) (* 4 (2^{P-1} f)))
    :rule-classes :linear)
  (defrule !c-type-when-finite-positive-binary
    (implies (finite-positive-binary-p v f)
             (and (integerp (!c v f))
                  (< 1 (!c v f))))
    :rule-classes :type-prescription)
  (acl2::with-arith5-help
   (defrule !c*2^!q-as-v
     (equal (* (!c v f) (expt 2 (!q v f)))
            (pos-rational-fix v))
     :enable (!q c))))

(define !cr
  ((x pos-rationalp)
   (f formatp))
  :returns (!cr pos-rationalp :rule-classes ())
  (let ((q (q x f))
        (c (c x f)))
    (if (or (= q (Qmin f)) (not (= c (2^{P-1} f))))
        (+ (!c x f) 1)
      (+ (!c x f) 2)))
  ///
  (fty::deffixequiv !cr)
  (defrule !cr-linear
    (<= (!cr x f) (+ 2 (* 4 (2^{P-1} f))))
    :rule-classes :linear)
  (defrule !cr-type-when-finite-positive-binary
    (implies (finite-positive-binary-p v f)
             (and (integerp (!cr v f))
                  (< 1 (!cr v f))))
    :rule-classes :type-prescription)
  (acl2::with-arith5-help
   (defrule !cr*2^!q-as-vr
     (equal (* (!cr v f) (expt 2 (!q v f)))
            (vr v f))
     :enable (!q !c c vr))))

(define !cl
  ((x pos-rationalp)
   (f formatp))
  :returns (!cl rationalp :rule-classes ())
  (- (!c x f) 1)
  ///
  (fty::deffixequiv !cl)
  (defrule !cl-linear
    (<= (!cl x f) (+ -1 (* 4 (2^{P-1} f))))
    :rule-classes :linear)
  (defrule !cl-type-when-finite-positive-binary
    (implies (finite-positive-binary-p v f)
             (posp (!cl v f)))
    :rule-classes :type-prescription)
  (acl2::with-arith5-help
   (defrule !cl*2^!q-as-vl
     (equal (* (!cl v f) (expt 2 (!q v f)))
            (vl v f))
     :enable (!q !c vl-alt))))
