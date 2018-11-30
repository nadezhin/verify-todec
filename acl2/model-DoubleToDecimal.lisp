;; ACL2 models of Java methods from Rafaello Guilietti's math.DoubleToDecimal
;;
(in-package "RTL")
(include-book "model-support")
(include-book "model-MathUtils")
(include-book "section5")
(include-book "round-newmann")

(local (acl2::allow-arith5-help))

(local (include-book "rtl/rel11/support/bits" :dir :system))
(local (include-book "rtl/rel11/support/float" :dir :system))
(local (include-book "rtl/rel11/support/reps" :dir :system))
(local (include-book "centaur/gl/gl" :dir :system))
(local (include-book "alpha-separated-format"))

(local
 (acl2::with-arith5-help
  (defruled bits-as-loghead-logtail
    (implies (and (integerp x)
                  (integerp i)
                  (natp j))
             (equal (bits x i j)
                    (acl2::loghead (+ 1 i (- j)) (acl2::logtail j x))))
    :enable (bits fl))))

(encapsulate ()
  (local (include-book "centaur/bitops/ihsext-basics" :dir :system))

  (defrule ubyte64p-loghead-64
    (acl2::ubyte64p (acl2::loghead 64 x))
    :enable acl2::ubyte64p)

  (defrule loghead-64-longfix
    (equal (acl2::loghead 64 (long-fix x))
           (acl2::loghead 64 x))
    :enable long-fix)

  (defrule logbitp-0-longfix
    (equal (acl2::logbitp 0 (long-fix x))
           (acl2::logbitp 0 x))
    :enable long-fix)

  (defrule logbitp-0-loghead-64
    (equal (acl2::logbitp 0 (acl2::loghead 64 x))
           (acl2::logbitp 0 x)))

  (defrule longfix-loghead-64
    (equal (long-fix (acl2::loghead 64 x))
           (long-fix x))
    :enable long-fix))

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

(define bq<BQ_MASK@
  ((enc acl2::ubyte64p))
  :returns (yes booleanp :rule-classes ())
  (if_icmpge (bq@ enc) *DoubleToDecimal.BQ_MASK*)
  ///
  (fty::deffixequiv bq<BQ_MASK@)
  (defruled bq<BQ_MASK@-as-expf@
    (equal (bq<BQ_MASK@ enc)
           (< (expf@ enc) #x7ff))
    :enable (bq@-as-expf@ if_icmpge sbyte32-suff))
  (defruled bq<BQ_MASK@-as-normp-denormp-zerp
    (equal (bq<BQ_MASK@ enc)
           (or (normp (enc@ enc) (dp))
               (denormp (enc@ enc) (dp))
               (zerp (enc@ enc) (dp))))
    :enable (bq<BQ_MASK@-as-expf@ expf@ normp denormp zerp dp)
    :use return-type-of-enc@))

(define bq>0@
  ((enc acl2::ubyte64p))
  :returns (yes booleanp :rule-classes ())
  (ifle (bq@ enc))
  ///
  (fty::deffixequiv bq>0@)
  (defruled bq>0@-as-expf@
    (equal (bq>0@ enc) (> (expf@ enc) 0))
    :enable (bq@-as-expf@ ifle sbyte32-suff)))

(define normp@
  ((enc acl2::ubyte64p))
  :returns (yes booleanp :rule-classes ())
  (and (bq<BQ_MASK@ enc) (bq>0@ enc))
  ///
  (fty::deffixequiv normp@)
  (defruled normp@-as-expf@
    (equal (normp@ enc)
           (and (< 0 (expf@ enc))
                (< (expf@ enc) #x7ff)))
    :enable (bq<BQ_MASK@-as-expf@ bq>0@-as-expf@))
  (defruled normp@-as-normp
    (equal (normp@ enc) (normp (enc@ enc) (dp)))
    :enable (bq<BQ_MASK@-as-expf@ bq>0@-as-expf@ expf@ normp dp)
    :use return-type-of-enc@))

(define bits==0x0000_0000_0000_0000L@
  ((enc acl2::ubyte64p))
  :returns (yes booleanp :rule-classes ())
  (acl2::b*
   ((bits==0x0000_0000_0000_0000L (lcmp (bits@ enc) #ux0000_0000_0000_0000)))
   (ifne bits==0x0000_0000_0000_0000L))
  ///
  (fty::deffixequiv bits==0x0000_0000_0000_0000L@)
  (defruled bits==0x0000_0000_0000_0000L@-as-sgnf-expf-sigf
    (equal (bits==0x0000_0000_0000_0000L@ enc)
           (and (= (sgnf@ enc) 0)
                (= (expf@ enc) 0)
                (= (manf@ enc) 0)))
    :enable (bits@-as-enc@
             sgnf@-as-logbit expf@-as-loghead-logtail manf@-as-loghead)
    :prep-lemmas
    ((gl::def-gl-rule lemma
       :hyp (acl2::ubyte64p enc)
       :concl (equal (ifne (lcmp (long-fix enc) 0))
                     (and (= (acl2::logbit 63 enc) 0)
                          (= (acl2::loghead 11 (acl2::logtail 52 enc)) 0)
                          (= (acl2::loghead 52 enc) 0)))
       :g-bindings (gl::auto-bindings (:nat enc 64)))))
  (defruled bits==0x0000_0000_0000_0000L@-as-zerp
    (equal (bits==0x0000_0000_0000_0000L@ enc)
           (and (zerp (enc@ enc) (dp))
                (not (sgn@ enc))))
    :enable (bits==0x0000_0000_0000_0000L@-as-sgnf-expf-sigf
             sgn@ expf@ manf@ sigf manf zerp dp)
    :disable bits==0x0000_0000_0000_0000L@
    :use return-type-of-enc@))

(define bits==0x8000_0000_0000_0000L@
  ((enc acl2::ubyte64p))
  :returns (yes booleanp :rule-classes ())
  (acl2::b*
   ((bits==0x8000_0000_0000_0000L (lcmp (bits@ enc) #ux-8000_0000_0000_0000)))
   (ifne bits==0x8000_0000_0000_0000L))
  ///
  (fty::deffixequiv bits==0x8000_0000_0000_0000L@)
  (defruled bits==0x8000_0000_0000_0000L@-as-sgnf-expf-sigf
    (equal (bits==0x8000_0000_0000_0000L@ enc)
           (and (= (sgnf@ enc) 1)
                (= (expf@ enc) 0)
                (= (manf@ enc) 0)))
    :enable (bits@-as-enc@
             sgnf@-as-logbit expf@-as-loghead-logtail manf@-as-loghead)
    :prep-lemmas
    ((gl::def-gl-rule lemma
       :hyp (acl2::ubyte64p enc)
       :concl (equal (ifne (lcmp (long-fix enc) #ux-8000_0000_0000_0000))
                     (and (= (acl2::logbit 63 enc) 1)
                          (= (acl2::loghead 11 (acl2::logtail 52 enc)) 0)
                          (= (acl2::loghead 52 enc) 0)))
       :g-bindings (gl::auto-bindings (:nat enc 64)))))
  (defruled bits==0x8000_0000_0000_0000L@-as-zerp
    (equal (bits==0x8000_0000_0000_0000L@ enc)
           (and (zerp (enc@ enc) (dp))
                (sgn@ enc)))
    :enable (bits==0x8000_0000_0000_0000L@-as-sgnf-expf-sigf
             sgn@ expf@ manf@ sigf manf zerp dp)
    :disable bits==0x8000_0000_0000_0000L@
    :use return-type-of-enc@))

(define denormp@
  ((enc acl2::ubyte64p))
  :returns (yes booleanp :rule-classes ())
  (and (bq<BQ_MASK@ enc)
       (not (bq>0@ enc))
       (not (bits==0x0000_0000_0000_0000L@ enc))
       (not (bits==0x8000_0000_0000_0000L@ enc)))
  ///
  (fty::deffixequiv denormp@)
  (defruled denormp@-as-expf-manf@
    (equal (denormp@ enc)
           (and (= (expf@ enc) 0)
                (not (= (manf@ enc) 0))))
    :enable (bq<BQ_MASK@-as-expf@
             bq>0@-as-expf@
             bits==0x0000_0000_0000_0000L@-as-sgnf-expf-sigf
             bits==0x8000_0000_0000_0000L@-as-sgnf-expf-sigf))
  (defruled denormp@-as-denormp
    (equal (denormp@ enc) (denormp (enc@ enc) (dp)))
    :enable (bq<BQ_MASK@-as-normp-denormp-zerp
             bq>0@-as-expf@
             bits==0x0000_0000_0000_0000L@-as-zerp
             bits==0x8000_0000_0000_0000L@-as-zerp
             expf@ denormp zerp dp)
    :use return-type-of-enc@))

(acl2::with-arith5-help
 (define v@
   ((enc acl2::ubyte64p))
   :returns (v@ (finite-positive-binary-p v@ (dp))
                :hints (("goal" :in-theory (e/d (normp@-as-normp
                                                 denormp@-as-denormp
                                                 dp)
                                                (abs)))))
   (if (or (normp@ enc) (denormp@ enc))
       (abs (decode (enc@ enc) (dp)))
     1)
   ///
   (fty::deffixequiv v@)
   (defrule v@-type
     (pos-rationalp (v@ enc))
     :rule-classes :type-prescription
     :disable v@
     :cases ((finite-positive-binary-p (v@ enc) (dp))))))

(define q@
  ((enc acl2::ubyte64p))
  :returns (q@ acl2::sbyte32p :rule-classes :type-prescription
               :hints (("goal" :in-theory (enable dp))))
  (cond ((normp@ enc)
         (iadd (- *DoubleToDecimal.Q_MIN* 1) (bq@ enc)))
        ((denormp@ enc)
         *DoubleToDecimal.Q_MIN*)
        (t (q 1 (dp))))
  ///
  (fty::deffixequiv q@)
  (defruled q@-as-q
    (equal (q@ enc)
           (q (v@ enc) (dp)))
    :enable (bq@-as-expf@
             normp@-as-expf@
             denormp@-as-expf-manf@
             expf@ manf@ expf manf sigf
             v@ q-c-decode dp
             )
    :disable abs
    :use lemma2
    :prep-lemmas
    ((defruled lemma2
       (equal (iadd -1075 (expf@ enc))
              (+ -1075 (expf@ enc)))
       :enable (iadd sbyte32-suff)
       :hints (("goal''" :in-theory (enable expf@))))))
  (defruled q@-linear
    (and (<= (Qmin (dp)) (q@ enc))
         (<= (q@ enc) (Qmax (dp))))
    :rule-classes :linear
    :enable q@-as-q
    :disable q@)
  (defrule q@-linear-corr
    (and (<= -1074 (q@ enc))
         (<= (q@ enc) 971))
    :rule-classes :linear
    :enable (q@-linear dp)
    :disable q@))

(define c@
  ((enc acl2::ubyte64p))
  :returns (c@ acl2::sbyte64p :rule-classes :type-prescription
               :hints (("goal" :in-theory (enable dp))))
  (cond ((normp@ enc)
         (acl2::b*
          ((bits&T_MASK (land (bits@ enc) *DoubleToDecimal.T_MASK*))
           (C_MIN!bits&T_MASK (lor *DoubleToDecimal.C_MIN* bits&T_MASK)))
          C_MIN!bits&T_MASK))
        ((denormp@ enc)
         (acl2::b*
          ((bits&T_MASK (land (bits@ enc) *DoubleToDecimal.T_MASK*)))
          bits&T_MASK))
        (t (c 1 (dp))))
  ///
  (fty::deffixequiv c@)
  (defruled c@-as-c
    (equal (c@ enc)
           (c (v@ enc) (dp)))
    :enable (bits@-as-enc@
             bq@-as-expf@
             normp@-as-expf@
             denormp@-as-expf-manf@
             manf@ expf@ manf expf sigf
             v@ q-c-decode dp)
    :disable (abs acl2::loghead acl2::logtail)
    :use ((:instance lemma (enc (enc@ enc)))
          (:instance manf@-as-loghead))
    :prep-lemmas
    ((gl::def-gl-ruled lemma
       :hyp (acl2::ubyte64p enc)
       :concl (and (equal (land (long-fix enc) #xfffffffffffff)
                          (acl2::loghead 52 enc))
                   (equal (lor #fx1p52 (acl2::loghead 52 enc))
                          (+ #fx1p52 (acl2::loghead 52 enc))))
       :g-bindings (gl::auto-bindings (:nat enc 64)))))
  (defruled c@-as-v@
    (equal (c@ enc)
           (* (v@ enc) (expt 2 (- (q@ enc)))))
    :enable (q@-as-q c@-as-c c)
    :disable c@)
  (defrule c@-type
    (posp (c@ enc))
    :rule-classes :type-prescription
    :enable c@-as-c
    :disable (c@ return-type-of-v@)
    :use ((:instance c-type-when-finite-positive-binary
                    (f (dp))
                    (x (v@ enc)))
          return-type-of-v@))
  (defrule c@-linear
    (<= (c@ enc) (CMax (dp)))
    :rule-classes :linear
    :enable c@-as-c
    :use (:instance c-linear-when-finite-positive-binary
                    (f (dp))
                    (x (v@ enc))))
  (defrule c@-linear-corr
    (<= (c@ enc) #x1fffffffffffff)
    :rule-classes :linear
    :enable dp
    :disable c@))

(define out@
  ((enc acl2::ubyte64p))
  :returns (out@ acl2::sbyte32p :rule-classes :type-prescription)
  (acl2::b*
   ((int-c (l2i (c@ enc)))
    (int-c&1 (iand int-c 1)))
   int-c&1)
  ///
  (fty::deffixequiv out@)
  (acl2::with-arith5-help
  (defruled out@-as-c@
    (equal (out@ enc)
           (if (not (integerp (* 1/2 (c@ enc)))) 1 0))
    :prep-lemmas
    ((gl::def-gl-rule lemma
       :hyp (unsigned-byte-p 53 c)
       :concl (equal (iand (l2i c) 1)
                     (acl2::logbit 0 c))
      :g-bindings (gl::auto-bindings (:nat c 53)))))))

(define c!=C_MIN@
  ((enc acl2::ubyte64p))
  :returns (c!=C_MIN@ acl2::sbyte32p)
  (if (ifeq (lcmp (c@ enc) *DoubleToDecimal.C_MIN*)) 1 0)
  ///
  (fty::deffixequiv c!=C_MIN@)
  (defruled c!=C_MIN@-as-c@
    (equal (c!=C_MIN@ enc)
           (if (= (c@ enc) (2^{P-1} (dp))) 0 1))
    :enable (lcmp ifeq signum dp)))

(define q==Q_MIN@
  ((enc acl2::ubyte64p))
  :returns (q==Q_MIN@ acl2::sbyte32p)
  (if (if_icmpne (q@ enc) *DoubleToDecimal.Q_MIN*) 1 0)
  ///
  (fty::deffixequiv q==Q_MIN@)
  (defruled q==Q_MIN@-as-q@
    (equal (q==Q_MIN@ enc)
           (if (= (q@ enc) (Qmin (dp))) 1 0))
    :enable (if_icmpne dp)))

(define regular@
  ((enc acl2::ubyte64p))
  :returns (yes booleanp :rule-classes ())
  (ifeq (ior (c!=C_MIN@ enc) (q==Q_MIN@ enc)))
  ///
  (fty::deffixequiv regular@)
  (defruled regular@-as-q-c@
    (equal (regular@ enc)
           (or (not (= (c@ enc) (2^{P-1} (dp))))
               (= (q@ enc) (Qmin (dp)))))
    :enable (c!=C_MIN@-as-c@ q==Q_MIN@-as-q@))
  (defruled c@-when-not-regular@
    (implies (not (regular@ enc))
             (equal (c@ enc) (2^{P-1} (dp))))
    :enable regular@-as-q-c@
    :disable regular@)
  (defruled wid-Rv-as-regular@
    (equal (wid-Rv (v@ enc) (dp))
           (* (if (regular@ enc) 1 3/4) (expt 2 (q@ enc))))
    :enable (regular@-as-q-c@ wid-Rv-as-c-q q@-as-q c@-as-c )
    :disable regular@))

(define qb@
  ((enc acl2::ubyte64p))
  :returns (qb@ integerp :rule-classes :type-prescription)
  (if (regular@ enc)
      (- (q@ enc) 1)
    (- (q@ enc) 2))
  ///
  (fty::deffixequiv qb@)
  (defrule qb@-linear
    (let ((f (dp)))
      (and (<= (1- (Qmin f)) (qb@ enc))
           (<= (qb@ enc) (1- (Qmax f)))))
    :rule-classes :linear
    :enable (regular@-as-q-c@
             q@-as-q))
  (defrule qb@-linear-corr
    (and (<= -1075 (qb@ enc))
         (<= (qb@ enc) 970))
    :rule-classes :linear
    :enable dp
    :disable qb@))

(define cb@
  ((enc acl2::ubyte64p))
  :returns (cb@ acl2::sbyte64p)
  (if (regular@ enc)
      (acl2::b*
       ((c<<1 (lshl (c@ enc) 1)))
       c<<1)
    (acl2::b*
     ((c<<2 (lshl (c@ enc) 2)))
     c<<2))
  ///
  (fty::deffixequiv cb@)
  (defruled cb@-as-q-c@
    (equal (cb@ enc)
           (* (if (regular@ enc) 2 4) (c@ enc)))
    :prep-lemmas
    ((gl::def-gl-rule lemma
       :hyp (unsigned-byte-p 53 c)
       :concl (and (equal (lshl c 1) (* 2 c))
                   (equal (lshl c 2) (* 4 c)))
       :g-bindings (gl::auto-bindings (:nat c 53)))))
  (acl2::with-arith5-help
   (defruled cb@-as-v@
     (equal (cb@ enc) (* (v@ enc) (expt 2 (- (qb@ enc)))))
     :enable (cb@-as-q-c@ c@-as-v@ qb@)
     :disable cb@))
  (defrule cb@-type
    (and (integerp (cb@ enc))
         (< 1 (cb@ enc)))
    :rule-classes :type-prescription
    :enable cb@-as-q-c@
    :disable cb@)
  (defruled cb@-linear
    (<= (cb@ enc) (* 4 (2^{P-1} (dp))))
    :rule-classes :linear
    :enable (cb@-as-q-c@ c@-when-not-regular@ CMax)
    :disable cb@)
  (defrule cb@-linear-corr
    (<= (cb@ enc) #fx1p54)
    :rule-classes :linear
    :enable (cb@-linear dp)
    :disable cb@))

(define cbr@
  ((enc acl2::ubyte64p))
  :returns (cbr@ acl2::sbyte64p)
  (if (regular@ enc)
      (acl2::b*
       ((cb+1 (ladd (cb@ enc) 1)))
       cb+1)
    (acl2::b*
     ((cb+2 (ladd (cb@ enc) 2)))
     cb+2))
  ///
  (fty::deffixequiv cbr@)
  (defruled cbr@-as-cb@
    (equal (cbr@ enc)
           (+ (cb@ enc) (if (regular@ enc) 1 2)))
    :enable (ladd sbyte64-suff))
  (acl2::with-arith5-help
   (defruled cbr@-as-vr
     (equal (cbr@ enc)
            (* (vr (v@ enc) (dp)) (expt 2 (- (qb@ enc)))))
     :enable (cbr@-as-cb@ cb@-as-q-c@  q@-as-q c@-as-c qb@ vr)
     :disable cbr@))
  (defrule cbr@-type
    (and (integerp (cbr@ enc))
         (< 1 (cbr@ enc)))
    :rule-classes :type-prescription
    :enable cbr@-as-cb@
    :disable cbr@)
  (defruled cbr@-linear
    (<= (cbr@ enc) (+ 2 (* 4 (2^{P-1} (dp)))))
    :rule-classes :linear
    :enable (cbr@-as-cb@ cb@-linear)
    :disable cbr@)
  (defrule cbr@-linear-corr
    (<= (cbr@ enc) #ux40_0000_0000_0002)
    :rule-classes :linear
    :enable (cbr@-linear dp)
    :disable cbr@))

(define k@
  ((enc acl2::ubyte64p))
  :returns (k@ acl2::sbyte32p)
  (if (regular@ enc)
      (MathUtils.flog10pow2 (q@ enc))
    (MathUtils.flog10threeQuartersPow2 (q@ enc)))
  ///
  (fty::deffixequiv k@)
  (defruled k@-as-wid-Rv
    (acl2::b*
     ((wid (wid-Rv (v@ enc) (dp))))
     (equal (k@ enc)
            (1- (ordD wid))))
    :enable (MathUtils.flog10pow2-as-ordD
             MathUtils.flog10threeQuartersPow2-as-ordD
             regular@-as-q-c@ wid-Rv-as-c-q q@-as-q c@-as-c sbyte32-suff dp)
    :use q@-linear)
  (defrule k@-linear
    (and (<= (- *MathUtils.MAX_EXP*) (k@ enc))
         (<= (k@ enc) (- *MathUtils.MIN_EXP*)))
    :rule-classes :linear
    :enable (wid-Rv<=max-ulp-when-finite-positive-binary
             wid-Rv>=MIN_VALUE k@-as-wid-Rv ordD (D) dp)
    :disable k@
    :use ((:instance expe-monotone
                     (b (D))
                     (x (MIN_VALUE (dp)))
                     (y (wid-Rv (v@ enc) (dp))))
          (:instance expe-monotone
                     (b (D))
                     (x (wid-Rv (v@ enc) (dp)))
                     (y (expt 2 (Qmax (dp)))))
          return-type-of-v@)))

(acl2::with-arith5-help
 (define alpha@
   ((enc acl2::ubyte64p))
   :returns (alpha@ pos-rationalp :rule-classes :type-prescription)
   (acl2::b*
    ((ulp2qb (expt 2 (qb@ enc)))
     (ulpD/2 (* 1/2 (expt (D) (k@ enc)))))
    (/ ulp2qb ulpD/2))
   ///
   (fty::deffixequiv alpha@)
   (acl2::with-arith5-nonlinear-help
    (defrule alpha@-linear
      (and (<= 2/3 (alpha@ enc))
           (< (alpha@ enc) (D)))
      :enable (k@-as-wid-Rv wid-Rv-as-regular@ qb@ ordD)
      :use ((:instance expe-lower-bound
                       (b (D))
                       (x (wid-Rv (v@ enc) (dp))))
            (:instance expe-upper-bound
                       (b (D))
                       (x (wid-Rv (v@ enc) (dp)))))))
   (acl2::with-arith5-nonlinear-help
    (defrule alpha@-linear-when-regular
      (implies (regular@ enc)
               (<= 1 (alpha@ enc)))
      :enable (k@-as-wid-Rv wid-Rv-as-regular@ qb@ ordD)
      :use (:instance expe-lower-bound
                      (b (D))
                      (x (wid-Rv (v@ enc) (dp))))))))

(define ord2alpha@
   ((enc acl2::ubyte64p))
   :returns (alpha@ acl2::sbyte32p)
   (if (regular@ enc)
       (acl2::b*
        ((-k (ineg (k@ enc)))
         (flog2pow10{-k} (MathUtils.flog2pow10 -k))
         (q+flog2pow10{-k} (iadd (q@ enc) flog2pow10{-k}))
         (q+flog2pow10{-k}+1 (iadd q+flog2pow10{-k} 1)))
        q+flog2pow10{-k}+1)
     (acl2::b*
      ((-k (ineg (k@ enc)))
       (flog2pow10{-k} (MathUtils.flog2pow10 -k))
       (q+flog2pow10{-k} (iadd (q@ enc) flog2pow10{-k})))
      q+flog2pow10{-k}))
   ///
   (fty::deffixequiv ord2alpha@)
   (acl2::with-arith5-help
    (defruled ord2alpha@-as-alpha@
      (equal (ord2alpha@ enc)
             (ord2 (alpha@ enc)))
      :enable (MathUtils.flog2pow10-as-ord2
               ineg iadd sbyte32-suff
               alpha@ qb@ ord2 expe-shift)
      :use k@-linear
      :prep-lemmas
      ((defrule expe-D^{-k}-linear
         (and (<= -971 (expe (expt (D) (- (k@ enc))) 2))
              (<= (expe (expt (D) (- (k@ enc))) 2) 1076))
         :rule-classes :linear
         :use ((:instance expe-monotone
                          (x (expt (D) *MathUtils.MIN_EXP*))
                          (y (expt (D) (- (k@ enc))))
                          (b 2))
               (:instance expe-monotone
                          (x (expt (D) (- (k@ enc))))
                          (y (expt (D) *MathUtils.MAX_EXP*))
                          (b 2)))
         :prep-lemmas
         ((defrule lemma
            (and (equal (expe (expt (D) *MathUtils.MIN_EXP*) 2) -971)
                 (equal (expe (expt (D) *MathUtils.MAX_EXP*) 2) 1076))
            :enable ((D))))))))
   (defrule ord2alpha@-linear
     (and (<= 0 (ord2alpha@ enc))
          (<= (ord2alpha@ enc) 4))
     :rule-classes :linear
     :enable (ord2alpha@-as-alpha@ ord2 (D))
     :use (alpha@-linear
           (:instance expe-monotone
                      (x 2/3)
                      (y (alpha@ enc))
                      (b 2))
           (:instance expe-monotone
                      (x (alpha@ enc))
                      (y (D))
                      (b 2))))
   (defrule ord2alpha@-when-regular
     (implies (regular@ enc)
              (<= 1 (ord2alpha@ enc)))
     :rule-classes :linear
     :enable (ord2alpha@-as-alpha@ ord2)
     :use (:instance expe-monotone
                     (x 1)
                     (y (alpha@ enc))
                     (b 2))))

(define delta@
   ((enc acl2::ubyte64p))
   :returns (delta@ acl2::sbyte32p)
   (if (regular@ enc)
       (acl2::b*
        ((61-q (isub 61 (q@ enc)))
         (-k (ineg (k@ enc)))
         (flog2pow10{-k} (MathUtils.flog2pow10 -k))
         (61-q-flog2pow10{-k} (isub 61-q flog2pow10{-k})))
        61-q-flog2pow10{-k})
     (acl2::b*
      ((62-q (isub 62 (q@ enc)))
       (-k (ineg (k@ enc)))
       (flog2pow10{-k} (MathUtils.flog2pow10 -k))
       (62-q-flog2pow10{-k} (isub 62-q flog2pow10{-k})))
      62-q-flog2pow10{-k}))
   ///
   (fty::deffixequiv delta@)
   (acl2::with-arith5-help
    (defruled delta@-as-ord2alpha@
      (equal (delta@ enc)
             (- 62 (ord2alpha@ enc)))
      :enable (MathUtils.flog2pow10-as-ord2
               ineg isub sbyte32-suff
               alpha@ ord2alpha@-as-alpha@ qb@ ord2 expe-shift)
      :use k@-linear
      :prep-lemmas
      ((defrule expe-D^{-k}-linear
         (and (<= -971 (expe (expt (D) (- (k@ enc))) 2))
              (<= (expe (expt (D) (- (k@ enc))) 2) 1076))
         :rule-classes :linear
         :use ((:instance expe-monotone
                          (x (expt (D) *MathUtils.MIN_EXP*))
                          (y (expt (D) (- (k@ enc))))
                          (b 2))
               (:instance expe-monotone
                          (x (expt (D) (- (k@ enc))))
                          (y (expt (D) *MathUtils.MAX_EXP*))
                          (b 2)))
         :prep-lemmas
         ((defrule lemma
            (and (equal (expe (expt (D) *MathUtils.MIN_EXP*) 2) -971)
                 (equal (expe (expt (D) *MathUtils.MAX_EXP*) 2) 1076))
            :enable ((D))))))))
   (defrule delta@-linear
     (and (<= 58 (delta@ enc))
          (<= (delta@ enc) 62))
     :rule-classes :linear
     :enable delta@-as-ord2alpha@)
   (defrule delta@-when-regular
     (implies (regular@ enc)
              (<= (delta@ enc) 61))
     :rule-classes :linear
     :enable delta@-as-ord2alpha@))

(define cbl@
  ((enc acl2::ubyte64p))
  :returns (cbr@ acl2::sbyte64p)
  (acl2::b*
   ((cb-1 (lsub (cb@ enc) 1)))
   cb-1)
  ///
  (fty::deffixequiv cbl@)
  (defruled cbl@-as-cb@
    (equal (cbl@ enc) (- (cb@ enc) 1))
    :enable (lsub sbyte64-suff))
  (acl2::with-arith5-help
   (defruled cbl@-as-vl
     (equal (cbl@ enc)
            (* (vl (v@ enc) (dp)) (expt 2 (- (qb@ enc)))))
     :enable (regular@-as-q-c@
              cbl@-as-cb@ cb@-as-q-c@ q@-as-q c@-as-c qb@ vl-alt)
     :disable cbl@))
  (defrule cbl@-type
    (posp (cbl@ enc))
    :rule-classes :type-prescription
    :enable cbl@-as-cb@
    :disable cbl@)
  (defruled cbl@-linear
    (<= (cbl@ enc) (+ -1 (* 4 (2^{P-1} (dp)))))
    :rule-classes :linear
    :enable (cbl@-as-cb@ cb@-linear)
    :disable cbl@)
  (defrule cbl@-linear-corr
    (<= (cbl@ enc) #ux3f_ffff_ffff_ffff)
    :rule-classes :linear
    :enable (cbl@-linear dp)
    :disable cbl@))

(define g1@
  ((enc acl2::ubyte64p))
  :returns (g1@ acl2::sbyte64p
                :hints (("goal" :in-theory
                         (enable MathUtils.floorPow10p1dHigh-as-floorPow10
                                 ineg sbyte32-suff))))
  (acl2::b*
   ((-k (ineg (k@ enc)))
    (floorPow10p1dHigh{-k} (MathUtils.floorPow10p1dHigh -k)))
   floorPow10p1dHigh{-k})
  ///
  (fty::deffixequiv g1@)
  (defruled g1@-as-floorPow10p1
    (equal (g1@ enc) (acl2::logtail 63 (floorPow10p1 (- (k@ enc)))))
    :enable (MathUtils.floorPow10p1dHigh-as-floorPow10p1 ineg sbyte32-suff)
    :disable acl2::logtail)
  (defrule g1@-type
    (natp (g1@ enc))
    :rule-classes :type-prescription
    :enable g1@-as-floorPow10p1)
  (defrule g1@-linear
    (< (g1@ enc) #fx1p63)
    :rule-classes :linear
    :enable (MathUtils.floorPow10p1dHigh-as-floorPow10 ineg sbyte32-suff)))


(define g0@
  ((enc acl2::ubyte64p))
  :returns (g0@ acl2::sbyte64p
                :hints (("goal" :in-theory
                         (enable MathUtils.floorPow10p1dLow-as-floorPow10p1
                                 ineg sbyte32-suff sbyte64-suff))))
  (acl2::b*
   ((-k (ineg (k@ enc)))
    (floorPow10p1dLow{-k} (MathUtils.floorPow10p1dLow -k)))
   floorPow10p1dLow{-k})
  ///
  (fty::deffixequiv g0@)
  (defruled g0@-as-floorPow10p1
    (equal (g0@ enc) (acl2::loghead 63 (floorPow10p1 (- (k@ enc)))))
    :enable (MathUtils.floorPow10p1dLow-as-floorPow10p1 ineg sbyte32-suff)
    :disable acl2::logtail)
  (defrule g0@-type
    (natp (g0@ enc))
    :rule-classes :type-prescription
    :enable g0@-as-floorPow10p1)
  (defrule g0@-linear
    (< (g0@ enc) #fx1p63)
    :rule-classes :linear
    :enable g0@-as-floorPow10p1))

(define cbSh@
  ((enc acl2::ubyte64p))
  :returns (cbSh@ acl2::sbyte32p)
  (iadd (ord2alpha@ enc) 2)
  ///
  (fty::deffixequiv cbSh@)
  (defruled cbSh@-as-ord2alpha@
    (equal (cbSh@ enc) (+ 2 (ord2alpha@ enc)))
    :enable (iadd sbyte32-suff))
  (defrule cbSh@-linear
    (and (<= 2 (cbSh@ enc))
         (<= (cbSh@ enc) 6))
    :rule-classes :linear
    :enable cbSh@-as-ord2alpha@)
  (defrule cbSh@-type
    (and (integerp (cbSh@ enc))
         (< 1 (cbSh@ enc)))
    :rule-classes :type-prescription
    :disable cbSh@)
  (defrule cbSh@-when-regular
    (implies (regular@ enc)
             (<= 3 (cbSh@ enc)))
    :rule-classes :linear
    :enable cbSh@-as-ord2alpha@))

(define cbArg@
  ((enc acl2::ubyte64p))
  :returns (cbArg@ acl2::sbyte64p)
  (lshl (cb@ enc) (cbSh@ enc))
  ///
  (fty::deffixequiv cbArg@)
  (acl2::with-arith5-help
   (defruled cbArg@-as-cb@-cbSh@
     (equal (cbArg@ enc)
            (* (cb@ enc) (expt 2 (cbSh@ enc))))
     :prep-lemmas
     ((gl::def-gl-rule lemma
         :hyp (and (unsigned-byte-p 55 cb)
                   (natp cbSh)
                   (<= cbSh 6))
         :concl (equal (lshl cb cbSh)
                       (ash cb cbSh))
         :g-bindings (gl::auto-bindings
                      (:nat cb 55)
                      (:nat cbSh 3))))))
  (acl2::with-arith5-nonlinear-help
   (defrule cbArg@-type
     (and (integerp (cbArg@ enc))
          (< 1 (cbArg@ enc)))
     :rule-classes :type-prescription
     :enable cbArg@-as-cb@-cbSh@
     :disable cbArg@))
  (acl2::with-arith5-help
   (defrule logbitp-0-cbArg@
     (not (logbitp 0 (cbArg@ enc)))
     :enable cbArg@-as-cb@-cbSh@
     :disable cbArg@
     :cases ((integerp (expt 2 (1- (cbSh@ enc)))))))
  (acl2::with-arith5-nonlinear-help
   (defrule cbArg@-linear
     (< (cbArg@ enc) #fx1p61)
     :rule-classes :linear
     :enable cbArg@-as-cb@-cbSh@
     :disable (cbArg@)
     :use cbSh@-linear))
  (acl2::with-arith5-help
   (defruled cbArg@-as-v@
     (equal (cbArg@ enc)
            (* (v@ enc)
               (expt 2 (+ 2 (ord2alpha@ enc) (- (qb@ enc))))))
     :enable (cbArg@-as-cb@-cbSh@ cb@-as-v@ cbSh@-as-ord2alpha@)
     :disable cbArg@)))

(define x0@
  ((enc acl2::ubyte64p))
  :returns (x0@ acl2::ubyte64p
                :hints (("goal" :in-theory (enable acl2::ubyte64p))))
  (acl2::loghead 64 (* (g0@ enc) (cbArg@ enc)))
  ///
  (fty::deffixequiv x0@)
  (defrule x0@-type
    (natp (x0@ enc))
    :rule-classes :type-prescription)
  (defrule x0@-linear
    (< (x0@ enc) #fx1p64)
    :rule-classes :linear))

(define x1@
  ((enc acl2::ubyte64p))
  :returns (x1@ acl2::sbyte64p)
  (acl2::b*
   ((multiplyHigh{g0?cb} (Math.multiplyHigh (g0@ enc) (cbArg@ enc))))
   multiplyHigh{g0?cb})
  ///
  (fty::deffixequiv x1@)
  (defruled x1@-as-cbArg@
    (equal (x1@ enc) (acl2::logtail 64 (* (g0@ enc) (cbArg@ enc)))))
  (defrule x1@-type
    (natp (x1@ enc))
    :rule-classes :type-prescription)
  (acl2::with-arith5-nonlinear-help
   (defrule x1@-linear
     (< (x1@ enc) #fx1p60)
     :rule-classes :linear)))

(acl2::with-arith5-help
 (defruled cbArg@*g0@-as-x0-x1
  (equal (* (cbArg@ enc) (g0@ enc))
         (+ (x0@ enc) (* #fx1p64 (x1@ enc))))
  :enable (x0@ x1@-as-cbArg@)
  :disable loghead-64-longfix
  :use (:instance loghead-64-longfix (x (* (cbArg@ enc) (g0@ enc))))))

(define y0@
  ((enc acl2::ubyte64p))
  :returns (y0@ acl2::sbyte64p)
  (acl2::b*
   ((g1*cb (lmul (g1@ enc) (cbArg@ enc))))
   g1*cb)
  ///
  (fty::deffixequiv y0@)
  (defruled y0@-as-cbArg@
    (equal (y0@ enc)
           (long-fix (* (g1@ enc) (cbArg@ enc))))
    :enable lmul)
  (acl2::with-arith5-help
   (defrule logbitp-0-loghead-64-y0@
     (not (acl2::logbitp 0 (acl2::loghead 64 (y0@ enc))))
     :enable (y0@-as-cbArg@)
     :disable (y0@ acl2::loghead acl2::logbitp)
     :prep-lemmas
     ((defrule lemma
        (implies (and (integerp cbarg)
                      (not (logbitp 0 cbarg))
                      (integerp g1))
                 (not (logbitp 0 (* cbarg g1)))))))))

(define y1@
  ((enc acl2::ubyte64p))
  :returns (y1@ acl2::sbyte64p)
  (acl2::b*
   ((multiplyHigh{g1?cb} (Math.multiplyHigh (g1@ enc) (cbArg@ enc))))
   multiplyHigh{g1?cb})
  ///
  (fty::deffixequiv y1@)
  (defruled y1@-as-cbArg@
    (equal (y1@ enc) (acl2::logtail 64 (* (g1@ enc) (cbArg@ enc)))))
  (defrule y1@-type
    (natp (y1@ enc))
    :rule-classes :type-prescription)
  (acl2::with-arith5-nonlinear-help
   (defrule y1@-linear
     (< (y1@ enc) #fx1p60)
     :rule-classes :linear)))

(acl2::with-arith5-help
 (defruled cbArg@*g1@-as-y0-y1
  (equal (* (cbArg@ enc) (g1@ enc))
         (+ (acl2::loghead 64 (y0@ enc)) (* #fx1p64 (y1@ enc))))
  :enable (y0@-as-cbArg@ y1@-as-cbArg@)
  :disable loghead-64-longfix
  :use (:instance loghead-64-longfix (x (* (cbArg@ enc) (g1@ enc))))))

(define z@
  ((enc acl2::ubyte64p))
  :returns (z@ acl2::sbyte64p)
  (acl2::b*
   ((y0>>>1 (lushr (y0@ enc) 1))
    ({y0>>>1}+x1 (ladd y0>>>1 (x1@ enc))))
   {y0>>>1}+x1)
  ///
  (fty::deffixequiv z@))

(define vbp@
  ((enc acl2::ubyte64p))
  :returns (vbp@ acl2::sbyte64p)
  (acl2::b*
   ((z>>>63 (lushr (z@ enc) 63))
    (y1+{z>>>63} (ladd (y1@ enc) z>>>63)))
   y1+{z>>>63})
  ///
  (fty::deffixequiv vbp@)
  (defruled vbp@-as-y1@-z@
    (equal (vbp@ enc)
           (+ (y1@ enc) (acl2::logbit 63 (z@ enc))))
    :prep-lemmas
    ((gl::def-gl-rule lemma
       :hyp (and (acl2::sbyte64p y1)
                 (natp y1)
                 (< y1 #fx1p60)
                 (acl2::sbyte64p z))
       :concl (equal (ladd y1 (lushr z 63))
                     (+ y1 (acl2::logbit 63 z)))
        :g-bindings (gl::auto-bindings
                     (:int y1 64)
                     (:int z 64)))))
  (defrule vbp@-type
    (natp (vbp@ enc))
    :rule-classes :type-prescription
    :enable vbp@-as-y1@-z@
    :disable vbp@)
  (defrule vbp@-linear
    (< (vbp@ enc) #fx1p62)
    :rule-classes :linear
    :enable vbp@-as-y1@-z@
    :disable vbp@))

(define p@
  ((enc acl2::ubyte64p))
  :returns (p@ natp :rule-classes :type-prescription)
  (+ (acl2::loghead 63 (z@ enc)) (ash (vbp@ enc) 63))
  ///
  (fty::deffixequiv p@)
  (acl2::with-arith5-help
   (defrule loghead-63-p@
     (equal (acl2::loghead 63 (p@ enc)) (acl2::loghead 63 (z@ enc)))))
  (acl2::with-arith5-help
   (defrule logtail-63-p@
     (equal (acl2::logtail 63 (p@ enc)) (vbp@ enc))))
  (acl2::with-arith5-help
   (defruled p@-as-cbArg@
     (equal (p@ enc)
            (acl2::logtail 64 (* (floorPow10p1 (- (k@ enc))) (cbArg@ enc))))
     :use ((:instance lemma
                      (enc (acl2::ubyte64-fix enc))
                      (x0 (x0@ enc))
                      (x1 (x1@ enc))
                      (y0 (acl2::loghead 64 (y0@ enc)))
                      (y1 (y1@ enc)))
           cbArg@*g0@-as-x0-x1
           cbArg@*g1@-as-y0-y1)
     :disable acl2::loghead
     :prep-lemmas
     ((acl2::with-arith5-help
       (defrule lemma0
         (equal (floorPow10p1 (- (k@ enc)))
                (+ (g0@ enc)
                   (ash (g1@ enc) 63)))
         :enable (g0@-as-floorPow10p1
                  g1@-as-floorPow10p1)))
      (gl::gl-set-uninterpreted x0@)
      (gl::gl-set-uninterpreted x1@)
      (gl::gl-set-uninterpreted y0@)
      (gl::gl-set-uninterpreted y1@)
      (gl::def-gl-ruled lemma
        :hyp (and (acl2::ubyte64p enc)
                  (acl2::ubyte64p x0)
                  (unsigned-byte-p 62 x1)
                  (acl2::ubyte64p y0)
                  (unsigned-byte-p 62 y1)
                  (equal (x0@ enc) x0)
                  (equal (x1@ enc) x1)
                  (equal (y0@ enc) (long-fix y0))
                  (equal (y1@ enc) y1))
        :concl (implies (not (logbitp 0 y0))
                        (equal (p@ enc)
                               (acl2::logtail 64 (+ x0
                                                    (ash x1 64)
                                                    (ash y0 63)
                                                    (ash y1 127)))))
        :g-bindings (gl::auto-bindings
                     (:nat enc 64)
                     (:mix (:seq (:nat x0 64) (:nat x1 62) (:skip 63))
                           (:seq (:skip 63) (:nat y0 64) (:nat y1 62)))))))
   (acl2::with-arith5-nonlinear-help
    (defrule p@-linear
      (< (p@ enc) #fx1p125)
      :rule-classes :linear
      :enable p@-as-cbArg@
      :disable p@))))

(define vb-inexact@
  ((enc acl2::ubyte64p))
  :returns (vn-inexact@ booleanp :rule-classes ())
  (acl2::b*
   ((z<<1 (lshl (z@ enc) 1))
    ({z<<1}!=0 (not (ifne (lcmp z<<1 0)))))
   {z<<1}!=0)
  ///
  (fty::deffixequiv vb-inexact@))

(define vb@
  ((enc acl2::ubyte64p))
  :returns (vb@ acl2::sbyte64p)
  (if (vb-inexact@ enc)
      (lor (vbp@ enc) 1)
    (vbp@ enc))
  ///
  (fty::deffixequiv vb@))

(define approx@
   ((enc acl2::ubyte64p))
   :returns (approx@ rationalp :rule-classes :type-prescription)
   (* #fx1p-128 (floorPow10p1 (- (k@ enc))) (cbArg@ enc))
   ///
   (fty::deffixequiv approx@)
   (acl2::with-arith5-help
    (defruled frac-approx@<=2^-64-as-p@
      (equal (<= #fx1p-64 (mod (approx@ enc) 1))
             (not (= (acl2::loghead 64 (p@ enc)) 0)))
      :enable p@-as-cbArg@
      :prep-lemmas
      ((defrule lemma
         (implies (integerp n)
                  (equal (<= #fx1p64 (mod n #fx1p128))
                         (not (= 0 (mod (floor n #fx1p64) #fx1p64)))))))))
   (acl2::with-arith5-help
    (defruled floor-approx@-as-p@
      (equal (floor (approx@ enc) 1)
             (acl2::logtail 64 (p@ enc)))
      :enable p@-as-cbArg@)))

(acl2::with-arith5-help
 (defruled vb@-as-round-Newmann-approx
   (equal (vb@ enc)
          (round-Newmann-approx (approx@ enc) #fx1p-64))
   :enable (round-Newmann-approx
            floor-approx@-as-p@
            vb@ vb-inexact@ p@)
   :disable acl2::logtail
   :use frac-approx@<=2^-64-as-p@
   :prep-lemmas
   ((gl::def-gl-rule lemma
      :hyp (and (acl2::sbyte64p z)
                (unsigned-byte-p 62 vbp))
      :concl (equal (if (ifne (lcmp (lshl z 1) 0)) vbp (lor vbp 1))
                    (let ((p  (+ (acl2::loghead 63 z) (ash vbp 63))))
                      (+ (* 2 (acl2::logtail 64 p))
                         (if (= (acl2::loghead 64 p) 0) 0 1))))
      :g-bindings (gl::auto-bindings
                   (:int z 64)
                   (:nat vbp 62))))))

(defruledl round-Newmann-approx-lemma
  (acl2::b*
   ((f (dp))
    (alpha*x (* (alpha@ enc) x))
    (CbMax (+ 2 (expt 2 (1+ (P f)))))
    (err (- approx alpha*x)))
   (implies
    (and (natp x)
         (real/rationalp approx)
         (<= x CbMax)
         (<= 0 err)
         (< err #fx1p-64))
    (equal (round-Newmann-approx approx #fx1p-64)
           (round-Newmann alpha*x))))
  :enable (round-Newmann-approx-correct q@-linear)
  :use (:instance alpha-separated-dp-correct
                  (q (q@ enc)))
  :prep-lemmas
  ((acl2::with-arith5-help
    (defrule lemma
      (equal (alpha@ enc)
             (if (regular@ enc)
                 (/ (expt 2 (q@ enc))
                    (expt (D) (1- (ordD (expt 2 (q@ enc))))))
               (/ (* 1/2 (expt 2 (q@ enc)))
                  (expt (D) (1- (ordD (* 3/4 (expt 2 (q@ enc)))))))))
      :enable (alpha@ k@-as-wid-Rv regular@-as-q-c@ wid-Rv-as-c-q q@-as-q c@-as-c
                      qb@)))))


(defruledl round-Newmann-approx-lemma-cb
  (equal (round-Newmann-approx (approx@ enc) #fx1p-64)
         (round-Newmann (* (alpha@ enc) (cb@ enc))))
  :use (:instance round-Newmann-approx-lemma
                  (x (cb@ enc))
                  (approx (approx@ enc)))
  :hints (("subgoal 3" :in-theory (enable dp))
          ("subgoal 2" :use lemma1)
          ("subgoal 1" :use lemma1))
  :prep-lemmas
  ((acl2::with-arith5-nonlinear-help
    (defruled lemma0
      (and (<= (* (1- (floorPow10p1 (- (k@ enc))))
                  (expt 2 (- (ord2alpha@ enc) 126)))
               (alpha@ enc))
           (< (alpha@ enc)
              (* (floorPow10p1 (- (k@ enc)))
                 (expt 2 (- (ord2alpha@ enc) 126)))))
      :enable (ord2alpha@-as-alpha@
               ord2 floorPow10p1 alpha@ qb@
               sigc sigm)
      :use (:instance fl-def
                      (x (sigc (expt (D) (- (k@ enc))) 126 2)))
      :prep-lemmas
      ((defrule expe-shift-alt
         (implies (and (rationalp x)
                       (not (= x 0))
                       (integerp n))
                  (equal (expe (* x (expt 2 n)) 2)
                         (+ n (expe x 2))))
         :use (:instance expe-shift (b 2))))))
   (acl2::with-arith5-nonlinear-help
    (defruled lemma1
      (and (<= (* (alpha@ enc) (cb@ enc)) (approx@ enc))
           (< (approx@ enc) (+ #fx1p-64 (* (alpha@ enc) (cb@ enc)))))
      :rule-classes ((:linear :trigger-terms ((approx@ enc))))
      :enable (approx@ p@-as-cbArg@ cbArg@-as-cb@-cbSh@ cbSh@-as-ord2alpha@)
      :disable acl2::logtail
      :use (lemma0 lemma3)
      :prep-lemmas
      ((acl2::with-arith5-nonlinear-help
        (defruled lemma-aaa
          (implies (and (posp 2^ord2alpha)
                        (<= 2^ord2alpha #fx1p4)
                        (natp cb)
                        (<= cb #fx1p54))
                   (<= (* 2^ord2alpha cb) #fx1p58))))
       (acl2::with-arith5-nonlinear++-help
        (defruled lemma-bbb
          (<= (expt 2 (ord2alpha@ enc)) 16)
          :use ord2alpha@-linear))
       (acl2::with-arith5-help
        (defruled lemma3
          (< (* (expt 2 (ord2alpha@ enc)) (cb@ enc)) #fx1p59)
          :enable lemma-bbb
          :use (:instance lemma-aaa
                          (2^ord2alpha (expt 2 (ord2alpha@ enc)))
                          (cb (cb@ enc))))))))))


(acl2::with-arith5-help
 (defrule vb@-as-round-Newmann
   (equal (vb@ enc)
          (round-Newmann (/ (v@ enc)
                            (* 1/2 (expt (D) (k@ enc))))))
   :enable (vb@-as-round-Newmann-approx alpha@ qb@ cb@-as-v@)
   :use round-Newmann-approx-lemma-cb))

(acl2::with-arith5-nonlinear-help
 (defrule vb@-as-round-Newmann-corr
   (implies (integerp m)
            (equal (signum (- (v@ enc) (* 1/2 m (expt (D) (k@ enc)))))
                   (signum (- (vb@ enc) (* 2 m)))))
   :use (:instance signum-round-Newmann
                   (x (/ (v@ enc) (* 1/2 (expt (D) (k@ enc))))))
   :enable signum))
