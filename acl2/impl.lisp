#|
(include-book "rtl/rel11/portcullis" :dir :system)
|#
(in-package "RTL")
(include-book "ihs/basic-definitions" :dir :system)
(include-book "kestrel/utilities/bytes" :dir :system)
(include-book "section11")

(local (include-book "rtl/rel11/support/basic" :dir :system))
(local (include-book "rtl/rel11/support/reps" :dir :system))

(local (acl2::allow-arith5-help))

(acl2::with-arith5-help
 (define s32
   ((x integerp))
   :returns (result acl2::sbyte32p
                    :hints (("goal" :in-theory (enable acl2::sbyte32p))))
   (acl2::logext 32 (ifix x))
   ///
   (fty::deffixequiv s32)
   (defrule s32-type
     (integerp (s32 x))
     :rule-classes :type-prescription)
   (defruled s32-when-sbyte32
     (implies (acl2::sbyte32p x)
              (equal (s32 x) x))
     :enable acl2::sbyte32p)))

(acl2::with-arith5-help
 (define s64
   ((x integerp))
   :returns (result acl2::sbyte64p
                    :hints (("goal" :in-theory (enable acl2::sbyte64p))))
   (acl2::logext 64 (ifix x))
   ///
   (fty::deffixequiv s64)
   (defrule s64-type
     (integerp (s64 x))
     :rule-classes :type-prescription)
   (defruled s64-when-sbyte64
     (implies (acl2::sbyte64p x)
              (equal (s64 x) x))
     :enable acl2::sbyte64p)))

(defruled sbyte32-suff
  (implies (and (integerp x)
                (<= #fx-1p31 x)
                (< x #fx1p31))
           (acl2::sbyte32p x))
  :enable acl2::sbyte32p)

(defruled sbyte64-suff
  (implies (and (integerp x)
                (<= #fx-1p63 x)
                (< x #fx1p63))
           (acl2::sbyte64p x))
  :enable acl2::sbyte64p)

(defrule sbyte32-fix-type
  (integerp (acl2::sbyte32-fix x))
  :rule-classes :type-prescription
  :enable acl2::sbyte32-fix)

(defrule sbyte64-fix-type
  (integerp (acl2::sbyte64-fix x))
  :rule-classes :type-prescription
  :enable acl2::sbyte64-fix)

(defrule sbyte32-is-integer
  (implies (acl2::sbyte32p x)
           (integerp x)))

(defrule sbyte64-is-integer
  (implies (acl2::sbyte64p x)
           (integerp x)))

(define Natural.compareTo
  ((this natp)
   (y natp))
  :returns (result acl2::sbyte32p)
  (acl2::b*
   ((this (nfix this))
    (y (nfix y)))
   (signum (- this y)))
  ///
  (fty::deffixequiv Natural.compareTo)
  (defrule Natural.compareTo-linear
    (and (<= -1 (Natural.compareTo this x))
         (<= (Natural.compareTo this x) 1))
    :rule-classes :linear))

(define Natural.closerTo
  ((this natp)
   (x natp)
   (y natp))
  :returns (result acl2::sbyte32p)
  (acl2::b*
   ((this (nfix this))
    (x (nfix x))
    (y (nfix y)))
   (signum (- (* 2 this) (+ x y))))
  ///
  (fty::deffixequiv Natural.closerTo)
  (defrule Natural.closerTo-linear
    (and (<= -1 (Natural.closerTo this x y))
         (<= (Natural.closerTo this x y) 1))
    :rule-classes :linear))

(acl2::with-arith5-help
 (define Natural.valueOfShiftLeft
   ((v acl2::sbyte64p)
    (n acl2::sbyte32p))
   :returns (result-or-exception (or (null result-or-exception)
                                     (natp result-or-exception))
                                 :rule-classes :type-prescription)
   (acl2::b*
    ((v (acl2::sbyte64-fix v))
     (n (acl2::sbyte32-fix n))
     ((unless (<= 0 n)) nil)
     (unsigned-v (acl2::loghead 64 v)))
    (ash unsigned-v n))
   ///
   (fty::deffixequiv Natural.valueOfShiftLeft)
   (defrule Natural.valueOfShiftLeft-type-noexception
     (implies (<= 0 (acl2::sbyte32-fix n))
              (natp (Natural.valueOfShiftLeft v n)))
     :rule-classes :type-prescription)
   (acl2::with-arith5-nonlinear-help
    (defrule Natural.valueOfShiftLeft-when-nonnegative
      (implies (and (<= 0 (acl2::sbyte64-fix v))
                    (<= 0 (acl2::sbyte32-fix n)))
               (equal (Natural.valueOfShiftLeft v n)
                      (* (acl2::sbyte64-fix v)
                         (expt 2 (acl2::sbyte32-fix n)))))
     :enable (acl2::sbyte64-fix acl2::sbyte64p)))))

(defconst *Powers.MAX_POW_10_EXP* 19)

(defconst *Powers.pow10*
  (list
   (expt (D) 0)
   (expt (D) 1)
   (expt (D) 2)
   (expt (D) 3)
   (expt (D) 4)
   (expt (D) 5)
   (expt (D) 6)
   (expt (D) 7)
   (expt (D) 8)
   (expt (D) 9)
   (expt (D) 10)
   (expt (D) 11)
   (expt (D) 12)
   (expt (D) 13)
   (expt (D) 14)
   (expt (D) 15)
   (expt (D) 16)
   (expt (D) 17)
   (expt (D) 18)
   (- (expt (D) 19) (expt 2 64))))

(defruled nth-pow10-when-i<=MAX_POW_10_EXP
  (implies (and (natp i)
                (< i (len *Powers.pow10*)))
           (equal (nth i *Powers.pow10*)
                  (s64 (expt (D) (nfix i)))))
  :enable ((D))
  :cases ((= i 0) (= i 1) (= i 2) (= i 3) (= i 4)
          (= i 5) (= i 6) (= i 7) (= i 8) (= i 9)
          (= i 10) (= i 11) (= i 12) (= i 13) (= i 14)
          (= i 15) (= i 16) (= i 17) (= i 18) (= i 19)))

(define Powers.pow10[]
  ((i acl2::sbyte32p))
  :returns (result-or-exception (or (null result-or-exception)
                                    (acl2::sbyte64p result-or-exception))
                                :hints (("goal" :use nth-pow10-when-i<=MAX_POW_10_EXP)))
  (acl2::b*
   ((i (acl2::sbyte32-fix i)))
   (and (natp i) (< i (len *Powers.pow10*)) (nth i *Powers.pow10*)))
  ///
  (fty::deffixequiv Powers.pow10[])
  (defrule Powers.pow10[]-type
    (or (null (Powers.pow10[] i))
        (integerp (Powers.pow10[] i)))
    :rule-classes :type-prescription)
  (defruled Powers.pow10[]-when-i<=MAX_POW_10_EXP
    (implies (and (natp i)
                  (<= i *Powers.MAX_POW_10_EXP*))
             (equal (Powers.pow10[] i)
                    (s64 (expt (D) i))))
    :enable acl2::sbyte32p
    :use (:instance nth-pow10-when-i<=MAX_POW_10_EXP))
  (defruled Powers.pow10[]-when-i<MAX_POW_10_EXP
    (implies (and (natp i)
                  (< i *Powers.MAX_POW_10_EXP*))
             (equal (Powers.pow10[] i)
                    (expt (D) i)))
    :enable ((D))
    :use (:instance nth-pow10-when-i<=MAX_POW_10_EXP)
    :cases ((= i 0) (= i 1) (= i 2) (= i 3) (= i 4)
            (= i 5) (= i 6) (= i 7) (= i 8) (= i 9)
            (= i 10) (= i 11) (= i 12) (= i 13) (= i 14)
            (= i 15) (= i 16) (= i 17) (= i 18))))


(fty::defprod DoubleToDecimal
  ((e acl2::sbyte32p)
   (q acl2::sbyte32p)
   (c acl2::sbyte64p)
   (lout acl2::sbyte32p)
   (rout acl2::sbyte32p)
   (buf character-listp)
   (index acl2::sbyte32p)))

(defconst *H* 17)

; stub of method DoubleToDecimal.toChars(long f, int e)
; returns positive rational instead of String
; TODO implement rendering to chars
(define DoubleToDecimal.toChars
  ((this DoubleToDecimal-p)
   (f acl2::sbyte64p)
   (e acl2::sbyte32p))
  :returns (result rationalp :rule-classes :type-prescription)
  (declare (ignore this))
  (acl2::b*
   ((f (acl2::sbyte64-fix f))
    (e (acl2::sbyte32-fix e)))
   (* f (expt (D) (- e *H*))))
  ///
  (fty::deffixequiv DoubleToDecimal.toChars)
  (acl2::with-arith5-help
   (defrule DoubleToDecimal.toChars-type-noexception
     (implies (< 0 (acl2::sbyte64-fix f))
              (pos-rationalp (DoubleToDecimal.toChars this f e)))
     :rule-classes :type-prescription)))
#|
(local
 (acl2::with-arith5-help
  (defrule mod-sbH-lemma
    (implies (and (acl2::sbyte64p sbH)
                  (<= 0 sbH)
                  (posp di))
             (acl2::sbyte64p (mod sbH di)))
    :enable acl2::sbyte64p)))

(local
 (acl2::with-arith5-help
  (defrule mod-sbH-lemma-2
    (implies (and (acl2::sbyte64p sbH)
                  (<= 0 sbH)
                  (posp di))
             (acl2::sbyte64p (- sbH (mod sbH di))))
    :enable acl2::sbyte64p)))

(local
 (acl2::with-arith5-nonlinear-help
  (defrule mod-sbH-lemma-3
    (implies (and (acl2::sbyte64p sbH)
                  (<= 0 sbH)
                  (< sbH (expt (D) *H*))
                  (posp di)
                  (<= di (expt (D) *H*))
                  )
             (acl2::sbyte64p (+ sbH
                                di
                                (- (mod sbH di)))))
    :enable (acl2::sbyte64p (D)))))

(local
 (defrule --g-lemma
   (implies (and (acl2::sbyte32p g)
                 (<= 0 g))
            (acl2::sbyte32p (1- g)))
   :enable acl2::sbyte32p
   ))
|#
(define v-dp
  ((this DoubleToDecimal-p))
  :returns (v (finite-positive-binary-p v (dp))
              :hints (("goal" :in-theory (enable (dp)))))
  (acl2::b*
   (((DoubleToDecimal this) this)
    (v (* this.c (expt 2 this.q))))
   (if (finite-positive-binary-p v (dp)) v 1))
  ///
  (fty::deffixequiv v-dp))

(define i-dp
  ((g acl2::sbyte32p))
  :returns (i posp :rule-classes :type-prescription)
  (acl2::b*
   ((g (acl2::sbyte32-fix g)))
   (if (and (<= 0 g)
            (< g *H*))
       (- *H* g)
     *H*))
  ///
  (fty::deffixequiv i-dp)
  (defrule i-dp-linear
    (<= (i-dp g) (H (dp)))
    :rule-classes :linear
    :enable ((dp))))

(acl2::with-arith5-help
 (defruled s_i-as-!s_i
   (implies (and (natp hi)
                 (< hi (H (dp))))
            (equal (- (s_i (H (dp)) v)
                      (acl2::sbyte64-fix (mod (s_i (H (dp)) v) (expt (D) hi))))
                   (!s_i (- (H (dp)) hi) v (dp))))
   :disable mod
   :expand (!s_i (H (dp)) v (dp))
   :use ((:instance !s_i-as-!s_H
                    (f (dp))
                    (i (- (H (dp)) hi)))
         (:instance mod-def
                    (x (!s_i (H (dp)) v (dp)))
                    (y (expt (D) hi))))
   :prep-lemmas
   ((defrule lemma
      (implies (and (integerp hi)
                    (natp sh)
                    (natp hi)
                    (< hi (H (dp))))
               (acl2::sbyte64p (mod sh (expt (D) hi))))
      :enable (acl2::sbyte64p (D) (dp))
      :use (:instance mod-bnd-1
                      (m sh)
                      (n (expt (D) hi)))))))

(acl2::with-arith5-nonlinear-help
 (defruled sbyte64p-!s_i
   (acl2::sbyte64p (!s_i i v (dp)))
   :enable (!s_i acl2::sbyte64p (dp) (D))
   :use (:instance s_i-linear
                   (i (min (H (dp)) (acl2::pos-fix i))))))

(acl2::with-arith5-help
 (defruled !s-i+D^{H-i}-as-!t_i
   (implies (and (<= (acl2::pos-fix i) (H f))
                 (= hi (- (H f) (acl2::pos-fix i)))
                 )
            (equal (+ (expt (D) hi) (!s_i i v f))
                   (!t_i i v f)))
   :enable (!s_i !t_i t_i)))

#|
(acl2::with-arith5-help
 (define DoubleToDecimal.fullCaseXS-loop-invariant
   ((this DoubleToDecimal-p)
    (g acl2::sbyte32p)
    (sbH acl2::sbyte64p)
    (p acl2::sbyte32p)
    (vb natp)
    (vbl natp)
    (vbr natp))
   :returns (yes booleanp :rule-classes ())
   (acl2::b*
    (((DoubleToDecimal this) this)
     (f (dp))
     (H (H f))
     ((unless (posp this.c)) nil)
     (v (* this.c (expt 2 this.q)))
     (e (e v))
     (!q (!q v f)))
    (and
     (<= (Qmin f) this.q)
     (<= this.q (Qmax f))
     (or (= this.q (Qmin f)) (<= (2^{P-1} f) this.c))
     (<= this.c (Cmax f))
     (natp g)
     (< g H)
     (finite-positive-binary-p v f)
     (= sbH (!s_i H v f))
     (<= 0 p)
     (<= e H)
     (= p (- e (+ H !q)))
     (= vb (vb v f))
     (= vbl (vbl v f))
     (= vbr (vbr v f))
     ))
   ///
   (defrule DoubleToDecimal.fullCaseXS-loop-invariant-fwd
     (implies (DoubleToDecimal.fullCaseXS-loop-invariant
               this g sbH p vb vbl vbr)
              (let ((f (dp))
                    (v (v-dp this)))
                (and (natp g)
                     (< g (H f))
                     (finite-positive-binary-p v f)
                     (= sbH (!s_i (H f) v f))
                     (= p (- (e v) (+ (H f) (!q v f))))
                     (= vb (vb v f))
                     (= vbl (vbl v f))
                     (= vbr (vbr v f)))))
     :rule-classes :forward-chaining
     :enable (v-dp Cmax)
     :use (:instance finite-positive-binary-suff
                     (f (dp))
                     (q (DoubleToDecimal->q this))
                     (c (DoubleToDecimal->c this))))
   (defrule i-dp-type-when-DoubleToDecimal.fullCaseXS-loop-invariant
     (implies (DoubleToDecimal.fullCaseXS-loop-invariant
               this g sbH p vb vbl vbr)
              (posp (i-dp g)))
     :rule-classes :type-prescription)
   (defrule i-dp-linear-when-DoubleToDecimal.fullCaseXS-loop-invariant
     (implies (DoubleToDecimal.fullCaseXS-loop-invariant
               this g sbH p vb vbl vbr)
              (<= (i-dp g) (H (dp))))
     :rule-classes :linear)
   (defrule v-dp-when-DoubleToDecimal.fullCaseXS-loop-invariant
     (implies (DoubleToDecimal.fullCaseXS-loop-invariant
               this g sbH p vb vbl vbr)
              (finite-positive-binary-p (v-dp this) (dp)))
     :enable DoubleToDecimal.fullCaseXS-loop-invariant-fwd)
   (defrule Power.pow10[]-g-when-DoubleToDecimal.fullCaseXS-loop-invariant
     (implies (DoubleToDecimal.fullCaseXS-loop-invariant
                    this g sbH p vb vbl vbr)
              (equal (Powers.pow10[] g)
                     (expt (D) (- (H (dp)) (i-dp g)))))
     :enable (i-dp (dp))
     :use (:instance Powers.pow10[]-when-i<MAX_POW_10_EXP
                     (i (acl2::sbyte32-fix g))))
   #|
   (defrule sbyte64-fix-sbH-when-DoubleToDecimal.fullCaseXS-loop-invariant
     (implies (DoubleToDecimal.fullCaseXS-loop-invariant
                    this g sbH p vb vbl vbr)
              (equal (acl2::sbyte64-fix sbH)
                     (s_i (H (dp)) (v-dp this))))
     :enable v-dp)
   (defrule sbyte32-fix-p-when-DoubleToDecimal.fullCaseXS-loop-invariant
     (implies (DoubleToDecimal.fullCaseXS-loop-invariant
                    this g sbH p vb vbl vbr)
              (equal (acl2::sbyte32-fix p)
                     (- (e (v-dp this)) (+ (H (dp)) (!q  (v-dp this) (dp))))))
     :enable v-dp)
   (defrule valueOfShiftLeft-!s_i-p-when-DoubleToDecimal.fullCaseXS-loop-invariant
     (implies (DoubleToDecimal.fullCaseXS-loop-invariant
                    this g sbH p vb vbl vbr)
              (equal (Natural.valueOfShiftLeft (!s_i (i-dp g) (v-dp this) (dp)) p)
                     (!u_i (i-dp g) (v-dp this) (dp))))
     :enable (!u_i !s_i S v-dp)
;     :enable (Natural.valueOfShiftLeft !u_i u_i !s_i S)
;     :disable acl2::loghead
     )
|#
     )
 )
|#
#|
(defrulel aaaaaaa
  (implies (DoubleToDecimal.fullCaseXS-loop-invariant
            this g sbH p vb vbl vbr)
           (acl2::sbyte64p sbH))
  :use DoubleToDecimal.fullCaseXS-loop-invariant

  )

(defrule e-linear-dp
   (implies (finite-positive-binary-p v (dp))
            (and (<= (Emin (dp)) (e v))
                 (<= (e v) (Emax (dp)))))
   :rule-classes :linear
   :use (:instance e-range-when-finite-positive-binary
                   (f (dp))))

(acl2::with-arith5-help
(defrule p-fits-in-sbyte32
   (implies (finite-positive-binary-p v (dp))
            (acl2::sbyte32p
             (+ (- (h (dp)))
                (e v)
                (- (!q v (dp))))))
   :enable ((dp))))
|#
(acl2::with-arith5-help
 (defrule loop-measure-decreases
   (implies (and (acl2::sbyte32p g)
                 (<= 0 g))
            (< (s32 (+ -1 g)) g))
   :enable s32))

(acl2::with-arith5-help
 (define DoubleToDecimal.fullCaseXS-loop
  ((this DoubleToDecimal-p)
   (g acl2::sbyte32p)
   (sbH acl2::sbyte64p)
   (p acl2::sbyte32p)
   (vb natp)
   (vbl natp)
   (vbr natp))
  :measure (nfix (+ (acl2::sbyte32-fix g) 1))
  :returns (result-or-exception (or (not result-or-exception)
                                    (rationalp result-or-exception))
                                :rule-classes :type-prescription)
  (acl2::b*
   (((DoubleToDecimal this) this)
    (g (acl2::sbyte32-fix g))
    (sbH (acl2::sbyte64-fix sbH))
    (p (acl2::sbyte32-fix p))
    (vb (nfix vb))
    (vbl (nfix vbl))
    (vbr (nfix vbr))

    ((unless (>= g 0)) nil) ; AssertionError
    (di (Powers.pow10[] g))
    ((unless di) nil) ; ArrayIndexOutOfBounds
    ((when (= di 0)) nil) ; DivideByZerorError
    (sbi (s64 (- sbH (s64 (mod sbH di)))))
    (ubi (Natural.valueOfShiftLeft sbi p))
    ((unless ubi) nil)
    (wbi (Natural.valueOfShiftLeft (s64 (+ sbi di)) p))
    ((unless wbi) nil)
    (uin (<= (s32 (+ (Natural.compareTo vbl ubi) 1)) 0))
    (win (<= (s32 (+ (Natural.compareTo wbi vbr) 1)) 0))
    ((when (and uin (not win)))
     (DoubleToDecimal.toChars this sbi this.e))
    ((when (and (not uin) win))
     (DoubleToDecimal.toChars this (s64 (+ sbi di)) this.e))
    ((when uin)
     (let ((cmp (Natural.closerTo vb ubi wbi)))
       (if (or (< cmp 0)
               (and (= cmp 0)
                    ; di=0 was checneed above
                    (= (s64 (logand (s64 (mod sbi di)) 1)) 0)))
           (DoubleToDecimal.toChars this sbi this.e)
         (DoubleToDecimal.toChars this (s64 (+ sbi di)) this.e)))))
   (DoubleToDecimal.fullCaseXS-loop
    this (s32 (- g 1)) sbH p vb vbl vbr))
  ))







