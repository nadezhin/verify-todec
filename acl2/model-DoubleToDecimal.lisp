;; ACL2 models of Java methods from Rafaello Guilietti's math.DoubleToDecimal
;;
(in-package "RTL")
(include-book "model-support")
(include-book "section3")

(local (acl2::allow-arith5-help))

(local (include-book "rtl/rel11/support/bits" :dir :system))
(local (include-book "centaur/gl/gl" :dir :system))

(local
 (acl2::with-arith5-help
  (defruled bits-as-loghead-logtail
    (implies (and (integerp x)
                  (integerp i)
                  (natp j))
             (equal (bits x i j)
                    (acl2::loghead (+ 1 i (- j)) (acl2::logtail j x))))
    :enable (bits fl))))

(defconst *Long.SIZE* 64)
(defconst *Double.SIZE* 64)

(define Double.doubleToRawLongBits
  ((enc acl2::ubyte64p))
  :returns (result acl2::sbyte64p)
  (long-fix (acl2::ubyte64-fix enc))
  ///
  (fty::deffixequiv Double.doubleToRawLongBits))

; Precision of normal values in bits.
(defconst *DoubleToDecimal.P* 53)

; Length in bits of the exponent field.
(defconst *DoubleToDecimal.W* (- (- *Double.SIZE* 1) (- *DoubleToDecimal.P* 1)))

; Minimum value of the exponent.
(defconst *DoubleToDecimal.Q_MIN* (+ (ash -1 (- *DoubleToDecimal.W* 1))
                                     (- *DoubleToDecimal.P*)
                                     3))

; Minimum value of the coefficient of a normal value.
(defconst *DoubleToDecimal.C_MIN* (ash 1 (- *DoubleToDecimal.P* 1)))

; Mask to extract the IEEE 754-2008 biased exponent.
(defconst *DoubleToDecimal.BQ_MASK* (- (ash 1 *DoubleToDecimal.W*) 1))

; Mask to extract the IEEE 754-2008 fraction bits.
(defconst *DoubleToDecimal.T_MASK* (- (ash 1 (- *DoubleToDecimal.P* 1)) 1))

; H = min {n integer | 10^(n-1) > 2^P}
(defconst *DoubleToDecimal.H* 17)

; used in the left-to-right extraction of the digits
(defconst *DoubleToDecimal.LTR* 28)
(defconst *DoubleToDecimal.MASK_LTR* (- (ash 1 *DoubleToDecimal.LTR*) 1))

(defconst *DoubleToDecimal.MASK_63* (- (ash 1 (- *Long.SIZE* 1)) 1))

(define enc@
  ((enc acl2::ubyte64p))
  :returns (enc@ (encodingp enc@ (dp))
                 :hints (("goal" :in-theory (enable encodingp
                                                    dp
                                                    acl2::ubyte64-fix
                                                    acl2::ubyte64p
                                                    bvecp))))
  (acl2::ubyte64-fix enc)
  ///
  (fty::deffixequiv enc@)
  (defrule enc@-type
    (natp (enc@ enc))
    :rule-classes :type-prescription
    :enable acl2::ubyte64-fix)
  (defrule enc@-linear
    (< (enc@ enc) #fx1p64)
    :rule-classes :linear
    :enable acl2::ubyte64-fix)
  (defrule ubyte64p-enc@
    (acl2::ubyte64p (enc@ enc))))

(define sgnf@
  ((enc acl2::ubyte64p))
  :returns (sgnf@ bitp :rule-classes :type-prescription
                  :hints (("goal" :in-theory (enable sgnf))))
  (sgnf (enc@ enc) (dp))
  ///
  (fty::deffixequiv sgnf@)
  (acl2::with-arith5-help
   (defruled sgnf@-as-logbit
     (equal (sgnf@ enc) (acl2::logbit 63 (enc@ enc)))
     :enable (sgnf (dp) bitn-def fl))))

(define sgn@
  ((enc acl2::ubyte64p))
  :returns (sgn@ booleanp :rule-classes :type-prescription)
  (= (sgnf@ enc) 1)
  ///
  (fty::deffixequiv sgn@)
  (defruled sgn@-as-logbitp
    (equal (sgn@ enc) (logbitp 63 (enc@ enc)))
    :enable sgnf@-as-logbit))

(define expf@
  ((enc acl2::ubyte64p))
  :returns (expf@ natp :rule-classes :type-prescription)
  (expf (enc@ enc) (dp))
  ///
  (fty::deffixequiv expf@)
  (defruled expf@-as-loghead-logtail
    (equal (expf@ enc)
           (acl2::loghead 11 (acl2::logtail 52 (enc@ enc))))
    :enable (bits-as-loghead-logtail (dp) expf))
  (acl2::with-arith5-help
   (defrule expf@-linear
     (< (expf@ enc) #fx1p11)
     :rule-classes ((:linear :trigger-terms ((expf@ enc))))
     :enable (expf@-as-loghead-logtail)))
  (defruled expf@-when-denormp
    (implies (denormp (enc@ enc) (dp))
             (equal (expf@ enc) 0))
    :enable denormp)
  (defruled expf@-when-normp
    (implies (normp (enc@ enc) (dp))
             (and (<= 1 (expf@ enc))
                  (<= (expf@ enc) 2046)))
    :rule-classes ((:linear :trigger-terms ((expf@ enc))))
    :enable (normp dp)))

(define manf@
  ((enc acl2::ubyte64p))
  :returns (manf@ natp :rule-classes :type-prescription)
  (manf (enc@ enc) (dp))
  ///
  (fty::deffixequiv manf@)
  (acl2::with-arith5-help
   (defruled manf@-as-loghead
     (equal (manf@ enc)
            (acl2::loghead 52 (enc@ enc)))
     :enable (bits-as-loghead-logtail (dp) manf)))
  (acl2::with-arith5-help
   (defrule manf@-linear
     (< (manf@ enc) #fx1p52)
     :rule-classes ((:linear :trigger-terms ((manf@ enc))))
     :enable (dp manf bvecp bits fl)))
  (defrule manf@-when-denormp
    (implies (denormp (enc@ enc) (dp))
             (posp (manf@ enc)))
    :rule-classes :type-prescription
    :enable (denormp dp sigf manf)))

(defruledl decode-when-denormp
  (implies (denormp (enc@ enc) (dp))
           (equal (decode (enc@ enc) (dp))
                  (* (if (= (sgnf@ enc) 1) -1 1)
                     (manf@ enc)
                     (expt 2 (Qmin (dp))))))
  :enable (sgnf@ manf@ decode ddecode denormp sigf manf dp)
  :cases ((= (sgnf@ enc) 0)
          (= (sgnf@ enc) 1)))

(local
 (acl2::with-arith5-help
  (defruled decode-when-normp
    (implies (normp (enc@ enc) (dp))
             (equal (decode (enc@ enc) (dp))
                    (* (if (= (sgnf@ enc) 1) -1 1)
                       (+ (2^{P-1} (dp)) (manf@ enc))
                       (expt 2 (+ -1 (Qmin (dp)) (expf@ enc))))))
    :enable (sgnf@ expf@ manf@ decode ndecode normp dp)
    :cases ((= (sgnf@ enc) 0)
            (= (sgnf@ enc) 1)))))

(acl2::with-arith5-help
 (define abs-val@
   ((enc acl2::ubyte64p))
   :returns (abs-val@ pos-rationalp
                      :rule-classes :type-prescription
                      :hints (("goal" :in-theory (enable decode-when-denormp
                                                         decode-when-normp))))
   (acl2::b*
    ((enc (enc@ enc))
     (f (dp)))
    (if (or (denormp enc f) (normp enc f))
        (abs (decode enc f))
      1))
   ///
   (fty::deffixequiv abs-val@)
   (defruled abs-val@-when-denormp
     (implies (denormp (enc@ enc) (dp))
              (equal (abs-val@ enc)
                     (* (manf@ enc)
                        (expt 2 (Qmin (dp))))))
     :enable decode-when-denormp)
   (defruled abs-val@-when-normp
     (implies (normp (enc@ enc) (dp))
              (equal (abs-val@ enc)
                     (* (+ (2^{P-1} (dp)) (manf@ enc))
                        (expt 2 (+ -1 (Qmin (dp)) (expf@ enc))))))
     :enable decode-when-normp)))

(define bits@
  ((enc acl2::ubyte64p))
  :returns (bits@ acl2::sbyte64p)
  (Double.doubleToRawLongBits enc)
  :guard-hints (("goal" :in-theory (enable (dp))))
  ///
  (fty::deffixequiv bits@)
  (acl2::with-arith5-help
   (defruled bits@-as-enc@
     (equal (bits@ enc) (long-fix (enc@ enc)))
     :enable (Double.doubleToRawLongBits enc@))))

(define bq@
  ((enc acl2::ubyte64p))
  :returns (bq@ acl2::sbyte32p)
  (acl2::b*
   ((bits>>>P-1 (lushr (bits@ enc) (- *DoubleToDecimal.P* 1)))
    (int-bits>>>P-1 (l2i bits>>>P-1))
    (int-bits>>>P-1&BQ_MASK (iand int-bits>>>P-1 *DoubleToDecimal.BQ_MASK*)))
   int-bits>>>P-1&BQ_MASK)
  ///
  (fty::deffixequiv bq@)
  (defruled bq@-as-expf@
    (equal (bq@ enc) (expf@ enc))
    :enable (expf@-as-loghead-logtail bits@-as-enc@)
    :prep-lemmas
    ((gl::def-gl-rule lemma
       :hyp (acl2::ubyte64p enc)
       :concl (equal (iand (l2i (lushr (long-fix enc) 52)) #x7ff)
                     (acl2::loghead 11 (acl2::logtail 52 enc)))
       :g-bindings (gl::auto-bindings (:nat enc 64))))))

(define q@
  ((enc acl2::ubyte64p))
  :returns (q@ acl2::sbyte32p :rule-classes :type-prescription)
  (if (> (bq@ enc) 0)
      (iadd (- *DoubleToDecimal.Q_MIN* 1) (bq@ enc))
    *DoubleToDecimal.Q_MIN*)
  ///
  (fty::deffixequiv q@)
  (defrule q@-denormp
    (implies (denormp (enc@ enc) (dp))
             (equal (q@ enc) (Qmin (dp))))
    :enable (denormp bq@-as-expf@ expf@ dp))
#|
  (acl2::with-arith5-help
   (defrule q@-normp-linear
     (implies (normp (enc@ enc) (dp))
              (and (<= (Qmin (dp)) (q@ enc))
                   (<= (q@ enc) (Qmax (dp)))))
     :rule-classes ((:linear :trigger-terms ((q@ enc))))
     :enable (normp bq@-as-expf@ expf@ iadd int-fix)))
|#
)
