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

(defconst *DoubleToDecimal.MASK_63* (-  (ash 1 63) 1))

(define DoubleToDecimal.rop
  ((g0 acl2::sbyte64p)
   (g1 acl2::sbyte64p)
   (cb acl2::sbyte64p))
  :returns (rop acl2::sbyte64p)
  (acl2::b*
   ((MASK_63 *DoubleToDecimal.MASK_63*)
    (x1 (Math.multiplyHigh g0 cb))
    (y0 (lmul g1 cb))
    (y1 (Math.multiplyHigh g1 cb))
    (z (ladd (lushr y0 1) x1))
    (vbp (ladd y1 (lushr z 63))))
   (lor vbp (lushr (ladd (land z MASK_63) MASK_63) 63)))
  ///
  (fty::deffixequiv DoubleToDecimal.rop)
  (acl2::with-arith5-help
   (defruled DoubleToDecimal.rop-as-round-Newmann-approx
     (implies (and (<= 0 (acl2::sbyte64-fix g0))
                   (<= 0 (acl2::sbyte64-fix g1))
                   (<= 0 (acl2::sbyte64-fix cb))
                   (evenp (acl2::sbyte64-fix cb)))
              (equal (DoubleToDecimal.rop g0 g1 cb)
                     (acl2::b*
                      ((g0 (acl2::sbyte64-fix g0))
                       (g1 (acl2::sbyte64-fix g1))
                       (cb (acl2::sbyte64-fix cb))
                       (g (+ g0 (ash g1 63)))
                       (approx (* #fx1p-128 g cb))
                       (threshold #fx1p-64))
                      (round-Newmann-approx approx threshold))))
     :enable (DoubleToDecimal.rop Math.multiplyHigh lmul)
     :disable (logbitp acl2::loghead acl2::logtail evenp)
     :prep-lemmas
     ((acl2::with-arith5-nonlinear-help
       (defrule lemma1
         (implies (and (acl2::sbyte64p x)
                       (acl2::sbyte64p y)
                       (<= 0 x)
                       (<= 0 y))
                  (< (* x y) #fx1p126))
         :enable acl2::sbyte64p))
      (defrule lemma2
        (implies (and (evenp cb)
                      (integerp g1))
                 (evenp (* cb g1))))
      (defrule lemma3
        (let ((p (* #fx1p128 approx)))
          (implies (integerp p)
                   (equal (round-newmann-approx approx #fx1p-64)
                          (+ (* 2 (acl2::logtail 128 p))
                             (if (<= #fx1p64 (acl2::loghead 128 p)) 1 0)))))
        :enable round-newmann-approx
        :disable acl2::|(* 2 (floor x y))|)
      (gl::def-gl-rule lemma4
         :hyp (and (unsigned-byte-p 126 g0*cb)
                   (unsigned-byte-p 126 g1*cb))
         :concl
         (acl2::b*
          ((MASK_63 *DoubleToDecimal.MASK_63*)
           (x1 (long-fix (acl2::logtail 64 g0*cb)))
           (y0 (long-fix g1*cb))
           (y1 (long-fix (acl2::logtail 64 g1*cb)))
           (z (ladd (lushr y0 1) x1))
           (vbp (ladd y1 (lushr z 63)))
           (rop (lor vbp (lushr (ladd (land z MASK_63) MASK_63) 63)))
           (p (+ g0*cb (ash g1*cb 63))))
          (implies (evenp g1*cb)
                   (equal rop
                          (+ (* 2 (acl2::logtail 128 p))
                             (if (<= #fx1p64 (acl2::loghead 128 p)) 1 0)))))
         :g-bindings (gl::auto-bindings
                      (:mix (:seq (:nat g0*cb 126) (:skip 63))
                            (:seq (:skip 63) (:nat g1*cb 126))))))))
  (defrule DoubleToDecimal.rop-type
    (implies (and (<= 0 (acl2::sbyte64-fix g0))
                  (<= 0 (acl2::sbyte64-fix g1))
                  (<= 0 (acl2::sbyte64-fix cb))
                  (evenp (acl2::sbyte64-fix cb)))
             (natp (DoubleToDecimal.rop g0 g1 cb)))
    :rule-classes :type-prescription
    :enable (DoubleToDecimal.rop-as-round-Newmann-approx
             round-Newmann-approx)
    :disable DoubleToDecimal.rop)
  (acl2::with-arith5-help
   (defrule DoubleToDecimal.rop-linear
     (implies (and (<= 0 (acl2::sbyte64-fix g0))
                   (<= 0 (acl2::sbyte64-fix g1))
                   (<= 0 (acl2::sbyte64-fix cb))
                   (evenp (acl2::sbyte64-fix cb)))
              (< (DoubleToDecimal.rop g0 g1 cb) #fx1p62))
     :rule-classes :linear
     :enable DoubleToDecimal.rop-as-round-Newmann-approx
     :disable DoubleToDecimal.rop
     :use (:instance lemma2
                     (g0 (acl2::sbyte64-fix g0))
                     (g1 (acl2::sbyte64-fix g1))
                     (cb (acl2::sbyte64-fix cb)))
     :prep-lemmas
     ((acl2::with-arith5-nonlinear-help
       (defrule lemma
         (implies (< approx #fx1p61)
                  (< (round-Newmann-approx approx threshold) #fx1p62))
         :rule-classes :linear
         :enable round-Newmann-approx
         :disable (acl2::|(* 1/2 (floor x y))| acl2::|(* 2 (floor x y))|)))
      (acl2::with-arith5-nonlinear-help
       (defruled lemma2
         (implies (and (acl2::sbyte64p g0)
                       (acl2::sbyte64p g1)
                       (acl2::sbyte64p cb)
                       (<= 0 g0)
                       (<= 0 g1)
                       (<= 0 cb))
                  (< (* (+ g0 (ash g1 63)) cb) #fx1p189))
         :enable acl2::sbyte64p))))))

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

(define shift@
   ((enc acl2::ubyte64p))
   :returns (alpha@ acl2::sbyte32p)
   (if (regular@ enc)
       (acl2::b*
        ((-k (ineg (k@ enc)))
         (flog2pow10{-k} (MathUtils.flog2pow10 -k))
         (q+flog2pow10{-k} (iadd (q@ enc) flog2pow10{-k}))
         (q+flog2pow10{-k}+3 (iadd q+flog2pow10{-k} 3)))
        q+flog2pow10{-k}+3)
     (acl2::b*
      ((-k (ineg (k@ enc)))
       (flog2pow10{-k} (MathUtils.flog2pow10 -k))
       (q+flog2pow10{-k} (iadd (q@ enc) flog2pow10{-k}))
       (q+flog2pow10{-k}+2 (iadd q+flog2pow10{-k} 2)))
      q+flog2pow10{-k}+2))
   ///
   (fty::deffixequiv shift@)
   (acl2::with-arith5-help
    (defruled shift@-as-alpha@
      (equal (shift@ enc)
             (+ 2 (ord2 (alpha@ enc))))
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
   (defruled shift@-as-ord2alpha@
     (equal (shift@ enc)
            (+ 2 (ord2alpha@ enc)))
     :enable (ord2alpha@-as-alpha@ shift@-as-alpha@))
   (defrule shift@-linear
     (and (<= 2 (shift@ enc))
          (<= (shift@ enc) 6))
     :rule-classes :linear
     :enable shift@-as-ord2alpha@)
   (defrule shift@-type
     (and (integerp (shift@ enc))
          (< 1 (shift@ enc)))
     :rule-classes :type-prescription
     :disable shift@)
   (defrule shift@-when-regular
     (implies (regular@ enc)
              (<= 3 (shift@ enc)))
     :rule-classes :linear
     :enable shift@-as-ord2alpha@))

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

(defruled aaaa
  (implies (and (<= 0 (acl2::sbyte64-fix cb))
                (evenp (acl2::sbyte64-fix cb)))
           (equal (DoubleToDecimal.rop (g0@ enc) (g1@ enc) cb)
                  (acl2::b*
                   ((cb (acl2::sbyte64-fix cb))
                    (g (floorPow10p1 (- (k@ enc))))
                    (approx (* #fx1p-128 g cb))
                    (threshold #fx1p-64))
                  (round-Newmann-approx approx threshold))))
  :enable DoubleToDecimal.rop-as-round-Newmann-approx
  :disable (acl2::loghead acl2::logtail ash)
  :prep-lemmas
  ((acl2::with-arith5-help
    (defrule lemma0
      (equal (floorPow10p1 (- (k@ enc)))
             (+ (g0@ enc) (ash (g1@ enc) 63)))
      :enable (g0@-as-floorPow10p1
               g1@-as-floorPow10p1)))))

(acl2::with-arith5-help
 (defruled aaaa2
    (implies (and (natp cb)
                (< cb #fx1p57))
           (equal (DoubleToDecimal.rop (g0@ enc) (g1@ enc) (lshl cb (shift@ enc)))
                 (acl2::b*
                  ((g (floorPow10p1 (- (k@ enc))))
                   (approx (* g cb (expt 2 (- (ord2alpha@ enc) 126))))
                   (threshold #fx1p-64))
                  (round-Newmann-approx approx threshold))))
    :enable (sbyte64-suff aaaa)
  :prep-lemmas
  ((defruled lemma0
     (<= (expt 2 (shift@ enc)) #fx1p6)
     :rule-classes :linear
     :cases ((<= (shift@ enc) 6)))
   (acl2::with-arith5-nonlinear-help
    (defrule lemma
      (implies (and (natp cb)
                    (< cb #fx1p57))
               (equal (lshl cb (shift@ enc))
                      (* cb (expt 2 (shift@ enc)))))
      :enable (lshl sbyte64-suff lemma0)))
   (acl2::with-arith5-nonlinear-help
    (defrule lemma2
      (implies (and (natp cb)
                    (< cb #fx1p57))
               (acl2::sbyte64p (* cb (expt 2 (shift@ enc)))))
      :enable (sbyte64-suff lemma0)))
   (defrule lemma3
     (equal (ord2alpha@ enc)
            (- (shift@ enc) 2))
     :enable shift@-as-ord2alpha@))))

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

(local
 (acl2::with-arith5-help
  (defruled round-Newmann-approx-lemma-cb
  (implies (and (natp cb)
                (<= cb (+ 2 (expt 2 (1+ (P (dp)))))))
           (let ((approx (* cb
                            (floorPow10p1 (- (k@ enc)))
                            (expt 2 (- (ord2alpha@ enc) 126)))))
             (equal (round-Newmann-approx approx #fx1p-64)
                    (round-Newmann (* (alpha@ enc) cb)))))
  :use (:instance round-Newmann-approx-lemma
                  (x cb)
                  (approx (* cb
                            (floorPow10p1 (- (k@ enc)))
                            (expt 2 (- (ord2alpha@ enc) 126)))))
  :hints (("subgoal 2" :use lemma1)
          ("subgoal 1" :use lemma1))
  :prep-lemmas
  ((defrule lemma00
     (< (+ 2 (expt 2 (1+ (P (dp))))) #fx1p56)
     :rule-classes :linear
     :enable dp)
   (acl2::with-arith5-nonlinear-help
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
      (let ((approx (* cb
                       (floorPow10p1 (- (k@ enc)))
                       (expt 2 (- (ord2alpha@ enc) 126)))))
        (implies (and (natp cb)
                      (< cb #fx1p56))
                 (and (<= (* (alpha@ enc) cb) approx)
                      (< approx (+ #fx1p-64 (* (alpha@ enc) cb))))))
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
          (implies (and (natp cb)
                        (< cb #fx1p56))
                   (< (* (expt 2 (- (ord2alpha@ enc) 126)) cb) #fx1p-64))
          :enable lemma-bbb
          :cases ((<= (ord2alpha@ enc) 4))
          :use (:instance lemma-aaa
                          (2^ord2alpha (expt 2 (ord2alpha@ enc)))))))))))))

(acl2::with-arith5-help
 (defruled aaaa3
   (implies
    (and (natp cb)
         (<= cb (+ 2 (* 4 (2^{P-1} (dp))))))
    (equal (DoubleToDecimal.rop (g0@ enc) (g1@ enc) (lshl cb (shift@ enc)))
           (round-Newmann (* (alpha@ enc) cb))))
   :enable (round-Newmann-approx-lemma-cb aaaa2 2^{P-1})
   :prep-lemmas
   ((defrule lemma00
      (< (+ 2 (expt 2 (1+ (P (dp))))) #fx1p56)
      :rule-classes :linear
      :enable dp))))

(define vb@
  ((enc acl2::ubyte64p))
  :returns (vb@ acl2::sbyte64p)
  (acl2::b*
   ((cb<<shift (lshl (cb@ enc) (shift@ enc))))
   (DoubleToDecimal.rop (g0@ enc) (g1@ enc) cb<<shift))
  ///
  (fty::deffixequiv vb@)
  (defrule vb@-as-round-Newmann
    (equal (vb@ enc)
           (round-Newmann (* (alpha@ enc) (cb@ enc))))
    :enable (aaaa3 cb@-linear)))

(define vbl@
  ((enc acl2::ubyte64p))
  :returns (vbl@ acl2::sbyte64p)
  (acl2::b*
   ((cbl<<shift (lshl (cbl@ enc) (shift@ enc))))
   (DoubleToDecimal.rop (g0@ enc) (g1@ enc) cbl<<shift))
  ///
  (fty::deffixequiv vbl@)
  (defrule vbl@-as-round-Newmann
    (equal (vbl@ enc)
           (round-Newmann (* (alpha@ enc) (cbl@ enc))))
    :enable (aaaa3 cbl@-linear)))

(define vbr@
  ((enc acl2::ubyte64p))
  :returns (vbr@ acl2::sbyte64p)
  (acl2::b*
   ((cbr<<shift (lshl (cbr@ enc) (shift@ enc))))
   (DoubleToDecimal.rop (g0@ enc) (g1@ enc) cbr<<shift))
  ///
  (fty::deffixequiv vbr@)
  (defrule vbr@-as-round-Newmann
    (equal (vbr@ enc)
           (round-Newmann (* (alpha@ enc) (cbr@ enc))))
    :enable (aaaa3 cbr@-linear)))

(acl2::with-arith5-help
 (defrule vb@-as-round-Newmann-2
   (equal (vb@ enc)
          (round-Newmann (/ (v@ enc)
                            (* 1/2 (expt (D) (k@ enc))))))
   :enable (alpha@ cb@-as-v@)
   :use vb@-as-round-Newmann))

(acl2::with-arith5-nonlinear-help
 (defrule vb@-as-round-Newmann-corr
   (implies (integerp m)
            (equal (signum (- (v@ enc) (* 1/2 m (expt (D) (k@ enc)))))
                   (signum (- (vb@ enc) (* 2 m)))))
   :use (:instance signum-round-Newmann
                   (x (/ (v@ enc) (* 1/2 (expt (D) (k@ enc))))))
   :enable signum))

(acl2::with-arith5-help
 (defrule vbl@-as-round-Newmann-2
   (equal (vbl@ enc)
          (round-Newmann (/ (Vl (v@ enc) (dp))
                            (* 1/2 (expt (D) (k@ enc))))))
   :enable (alpha@ cbl@-as-Vl)
   :use vbl@-as-round-Newmann))

(acl2::with-arith5-nonlinear-help
 (defrule vbl@-as-round-Newmann-corr
   (implies (integerp m)
            (equal (signum (- (Vl (v@ enc) (dp)) (* 1/2 m (expt (D) (k@ enc)))))
                   (signum (- (vbl@ enc) (* 2 m)))))
   :use (:instance signum-round-Newmann
                   (x (/ (Vl (v@ enc) (dp)) (* 1/2 (expt (D) (k@ enc))))))
   :enable signum))

(acl2::with-arith5-help
 (defrule vbr@-as-round-Newmann-2
   (equal (vbr@ enc)
          (round-Newmann (/ (Vr (v@ enc) (dp))
                            (* 1/2 (expt (D) (k@ enc))))))
   :enable (alpha@ cbr@-as-Vr)
   :use vbr@-as-round-Newmann))

(acl2::with-arith5-nonlinear-help
 (defrule vbr@-as-round-Newmann-corr
   (implies (integerp m)
            (equal (signum (- (Vr (v@ enc) (dp)) (* 1/2 m (expt (D) (k@ enc)))))
                   (signum (- (vbr@ enc) (* 2 m)))))
   :use (:instance signum-round-Newmann
                   (x (/ (Vr (v@ enc) (dp)) (* 1/2 (expt (D) (k@ enc))))))
   :enable signum))
