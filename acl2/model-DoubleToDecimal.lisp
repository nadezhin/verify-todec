;; ACL2 models of Java methods from Rafaello Guilietti's math.DoubleToDecimal
;;
(in-package "RTL")
(include-book "model-support")
(include-book "model-MathUtils")
(include-book "section4")

(local (acl2::allow-arith5-help))

(local (include-book "rtl/rel11/support/bits" :dir :system))
(local (include-book "rtl/rel11/support/float" :dir :system))
(local (include-book "rtl/rel11/support/reps" :dir :system))
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

(define even@
  ((enc acl2::ubyte64p))
  :returns (yes booleanp :rule-classes ())
  (ifeq (ior (c!=C_MIN@ enc) (q==Q_MIN@ enc)))
  ///
  (fty::deffixequiv even@)
  (defruled even@-as-q-c@
    (equal (even@ enc)
           (or (not (= (c@ enc) (2^{P-1} (dp))))
               (= (q@ enc) (Qmin (dp)))))
    :enable (c!=C_MIN@-as-c@ q==Q_MIN@-as-q@))
  (defruled c@-when-not-even@
    (implies (not (even@ enc))
             (equal (c@ enc) (2^{P-1} (dp))))
    :enable even@-as-q-c@
    :disable even@)
  (defruled wid-Rv-as-even@
    (equal (wid-Rv (v@ enc) (dp))
           (* (if (even@ enc) 1 3/4) (expt 2 (q@ enc))))
    :enable (even@-as-q-c@ wid-Rv-as-c-q q@-as-q c@-as-c )
    :disable even@))

(define qb@
  ((enc acl2::ubyte64p))
  :returns (qb@ integerp :rule-classes :type-prescription)
  (if (even@ enc)
      (- (q@ enc) 1)
    (- (q@ enc) 2))
  ///
  (fty::deffixequiv qb@)
  (defrule qb@-linear
    (let ((f (dp)))
      (and (<= (1- (Qmin f)) (qb@ enc))
           (<= (qb@ enc) (1- (Qmax f)))))
    :rule-classes :linear
    :enable (even@-as-q-c@
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
  (if (even@ enc)
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
           (* (if (even@ enc) 2 4) (c@ enc)))
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
    :enable (cb@-as-q-c@ c@-when-not-even@ CMax)
    :disable cb@)
  (defrule cb@-linear-corr
    (<= (cb@ enc) #fx1p54)
    :rule-classes :linear
    :enable (cb@-linear dp)
    :disable cb@))

(define cbr@
  ((enc acl2::ubyte64p))
  :returns (cbr@ acl2::sbyte64p)
  (if (even@ enc)
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
           (+ (cb@ enc) (if (even@ enc) 1 2)))
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
    (<= (cbr@ enc) #x40000000000002)
    :rule-classes :linear
    :enable (cbr@-linear dp)
    :disable cbr@))

(define k@
  ((enc acl2::ubyte64p))
  :returns (k@ acl2::sbyte32p)
  (if (even@ enc)
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
             even@-as-q-c@ wid-Rv-as-c-q q@-as-q c@-as-c sbyte32-suff dp)
    :use q@-linear)
  (defrule k@-linear
    (and (<= (- *MathUtils.MAX_EXP*) (k@ enc))
         (<= (k@ enc) (- *MathUtils.MIN_EXP*)))
    :rule-classes :linear
    :enable (wid-Rv<=max-ulp-when-finite-positive-binary
             wid-Rv>=MIN_VALUE k@-as-wid-Rv dp)
    :disable k@
    :use ((:instance result-1-4
                     (x (MIN_VALUE (dp)))
                     (y (wid-Rv (v@ enc) (dp))))
          (:instance result-1-4
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
      :enable (k@-as-wid-Rv wid-Rv-as-even@ qb@)
      :use (:instance result-1-3
                      (x (wid-Rv (v@ enc) (dp)))
                      (k (ordD (wid-Rv (v@ enc) (dp)))))))
   (acl2::with-arith5-nonlinear-help
    (defrule alpha@-linear-when-even
      (implies (even@ enc)
               (<= 1 (alpha@ enc)))
      :enable (k@-as-wid-Rv wid-Rv-as-even@ qb@)
      :use (:instance result-1-3
                      (x (wid-Rv (v@ enc) (dp)))
                      (k (ordD (wid-Rv (v@ enc) (dp)))))))))

(define ord2alpha@
   ((enc acl2::ubyte64p))
   :returns (alpha@ acl2::sbyte32p)
   (if (even@ enc)
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
    (defrule ord2alpa@-as-alpha@
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
     :enable (ord2 (D))
     :use (alpha@-linear
           (:instance expe-monotone
                      (x 2/3)
                      (y (alpha@ enc))
                      (b 2))
           (:instance expe-monotone
                      (x (alpha@ enc))
                      (y (D))
                      (b 2))))
   (defrule ord2alpha@-when-even
     (implies (even@ enc)
              (<= 1 (ord2alpha@ enc)))
     :rule-classes :linear
     :enable ord2
     :use (:instance expe-monotone
                     (x 1)
                     (y (alpha@ enc))
                     (b 2))))

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
     :enable (even@-as-q-c@
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
    (<= (cbl@ enc) #x3fffffffffffff)
    :rule-classes :linear
    :enable (cbl@-linear dp)
    :disable cbl@))
