;; ACL2 models of some Java methods in Rafaello Guilietti's code contribution
;;
(in-package "RTL")
(include-book "ihs/basic-definitions" :dir :system)
(include-book "kestrel/utilities/fixbytes/instances" :dir :system)
(include-book "rtl/rel11/support/definitions" :dir :system)

(include-book "tools/with-arith5-help" :dir :system)
(local (acl2::allow-arith5-help))

(local (include-book "rtl/rel11/support/basic" :dir :system))

;; primitive types int and long

(acl2::with-arith5-help (define int-fix
   ((x integerp))
   :returns (result acl2::sbyte32p
                    :hints (("goal" :in-theory (enable acl2::sbyte32p))))
   (acl2::logext 32 (ifix x))
   ///
   (fty::deffixequiv int-fix)
   (defrule int-fix-type
     (integerp (int-fix x))
     :rule-classes :type-prescription)
   (defrule int-fix-when-sbyte32
     (implies (acl2::sbyte32p x)
              (equal (int-fix x) x))
     :enable acl2::sbyte32p)))

(acl2::with-arith5-help (define long-fix
   ((x integerp))
   :returns (result acl2::sbyte64p
                    :hints (("goal" :in-theory (enable acl2::sbyte64p))))
   (acl2::logext 64 (ifix x))
   ///
   (fty::deffixequiv long-fix)
   (defrule long-fix-type
     (integerp (long-fix x))
     :rule-classes :type-prescription)
   (defrule long-fix-when-sbyte64
     (implies (acl2::sbyte64p x)
              (equal (long-fix x) x))
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

(defrule sbyte32-is-acl2-numberp
  (implies (acl2::sbyte32p x)
           (acl2-numberp x)))

(defrule sbyte64-is-acl2-numberp
  (implies (acl2::sbyte64p x)
           (acl2-numberp x)))

;; ACL2 models of some JVM instructions

(define ldiv
  ((x acl2::sbyte64p)
   (y acl2::sbyte64p))
  :returns (result-or-exception (implies result-or-exception ; DivideByZeroError
                                         (acl2::sbyte64p result-or-exception)))
  (acl2::b*
   ((x (acl2::sbyte64-fix x))
    (y (acl2::sbyte64-fix y)))
   (and (not (= y 0)) (long-fix (truncate x y))))
  ///
  (fty::deffixequiv ldiv)
  (defrule sbyte64p-ldiv-noexcept
    (implies (not (= (acl2::sbyte64-fix y) 0))
             (acl2::sbyte64p (ldiv x y))))
  (defrule ldiv-type-noexcept
    (implies (not (= (acl2::sbyte64-fix y) 0))
             (integerp (ldiv x y)))
    :rule-classes :type-prescription)
  (defruled ldiv-when-nonnegative-args
    (implies (and (<= 0 (acl2::sbyte64-fix x))
                  (< 0 (acl2::sbyte64-fix y)))
             (equal (ldiv x y)
                    (fl (/ (acl2::sbyte64-fix x) (acl2::sbyte64-fix y)))))
    :use (:instance lemma
                    (x (acl2::sbyte64-fix x))
                    (y (acl2::sbyte64-fix y)))
    :prep-lemmas
    ((acl2::with-arith5-nonlinear-help
      (defrule lemma
        (implies (and (acl2::sbyte64p x)
                      (acl2::sbyte64p y)
                      (<= 0 x)
                      (< 0 y))
                 (equal (ldiv x y) (fl (/ x y))))
        :enable (acl2::sbyte64p fl)))))
  (acl2::with-arith5-help
   (defrule ldiv-type-when-nonnegative-args
     (implies (and (<= 0 (acl2::sbyte64-fix x))
                   (< 0 (acl2::sbyte64-fix y)))
              (natp (ldiv x y)))
     :rule-classes :type-prescription
     :disable ldiv
     :use ldiv-when-nonnegative-args)))

(define lrem
  ((x acl2::sbyte64p)
   (y acl2::sbyte64p))
  :returns (result-or-exception (implies result-or-exception ; DivideByZeroError
                                         (acl2::sbyte64p result-or-exception)))
  (acl2::b*
   ((x (acl2::sbyte64-fix x))
    (y (acl2::sbyte64-fix y)))
   (and (not (= y 0)) (long-fix (rem x y))))
  ///
  (fty::deffixequiv lrem)
  (defrule sbyte64p-lrem-noexcept
    (implies (not (= (acl2::sbyte64-fix y) 0))
             (acl2::sbyte64p (lrem x y))))
  (defrule lrem-type-noexcept
    (implies (not (= (acl2::sbyte64-fix y) 0))
             (integerp (lrem x y)))
    :rule-classes :type-prescription)
  (defruled lrem-when-nonnegative-args
    (implies (and (<= 0 (acl2::sbyte64-fix x))
                  (< 0 (acl2::sbyte64-fix y)))
             (equal (lrem x y)
                    (mod (acl2::sbyte64-fix x) (acl2::sbyte64-fix y))))
    :use (:instance lemma
                    (x (acl2::sbyte64-fix x))
                    (y (acl2::sbyte64-fix y)))
    :prep-lemmas
    ((acl2::with-arith5-nonlinear-help
      (defrule lemma
        (implies (and (acl2::sbyte64p x)
                      (acl2::sbyte64p y)
                      (<= 0 x)
                      (< 0 y))
                 (equal (lrem x y) (mod x y)))
        :enable acl2::sbyte64p))))
  (acl2::with-arith5-help
   (defrule lrem-type-when-nonnegative-args
     (implies (and (<= 0 (acl2::sbyte64-fix x))
                   (< 0 (acl2::sbyte64-fix y)))
              (natp (lrem x y)))
     :rule-classes :type-prescription
     :use lrem-when-nonnegative-args)))

(define lshl
  ((x acl2::sbyte64p)
   (y acl2::sbyte32p))
  :returns (results acl2::sbyte64p)
  (acl2::b*
   ((x (acl2::sbyte64-fix x))
    (y (acl2::sbyte32-fix y))
    (n (acl2::loghead 6 y)))
   (long-fix (ash x n)))
  ///
  (fty::deffixequiv lshl))


;; ACL2 models of math.Natural
;; these models are high level. They do not match actual code.

(acl2::with-arith5-help (define Natural.valueOfShiftLeft
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
   (defrule Natural.valueOfShiftLeft-noexception
     (implies (<= 0 (acl2::sbyte32-fix n))
              (Natural.valueOfShiftLeft v n)))
   (acl2::with-arith5-nonlinear-help
    (defrule Natural.valueOfShiftLeft-when-nonnegative
      (implies (and (<= 0 (acl2::sbyte64-fix v))
                    (<= 0 (acl2::sbyte32-fix n)))
               (equal (Natural.valueOfShiftLeft v n)
                      (* (acl2::sbyte64-fix v)
                         (expt 2 (acl2::sbyte32-fix n)))))
     :enable (acl2::sbyte64-fix acl2::sbyte64p)))))

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

(define Natural.multiply
  ((this natp)
   (y acl2::sbyte64p))
  :returns (result-or-exception (implies result-or-exception ; ArrayIndexOutOfBounds
                                         (natp result-or-exception)))
  (acl2::b*
   ((this (nfix this))
    (y (acl2::sbyte64-fix y)))
   (* this (acl2::loghead 64 y)))
  ///
  (fty::deffixequiv Natural.multiply)
  (acl2::with-arith5-help
   (defrule Natural.multiply-when-nonnegative
     (implies (<= 0 (acl2::sbyte64-fix y))
              (equal (Natural.multiply this y)
                     (* (nfix this)
                        (acl2::sbyte64-fix y))))
     :enable (acl2::sbyte64-fix acl2::sbyte64p))))

; The model differs from the actual code.
; Model raises exception when this < y.
; Code returns (this - y) mod 2^{32*len}
(define Natural.subtract
  ((this natp)
   (y natp))
  :returns (result-or-exception (implies result-or-exception ; should be AssertionError
                                         (natp result-or-exception)))
  (acl2::b*
   ((this (nfix this))
    (y (nfix y)))
   (and (<= y this)
        (- this y)))
  ///
  (fty::deffixequiv Natural.multiply)
  (defrule Natural.subtract-when-this>=y
    (implies (<= (nfix y) (nfix this))
             (equal (Natural.subtract this y)
                    (- (nfix this) (nfix y))))))

; TODO define more carefully when d[q] and d[q + 1] may be out of bounds
(define Natural.shiftRight
  ((this natp)
   (n acl2::sbyte32p))
  :returns (result-or-exception (implies result-or-exception
                                         (acl2::sbyte64p result-or-exception)))
  (acl2::b*
   ((this (nfix this))
    (n (acl2::sbyte32-fix n))
    ((unless (<= 0 n)) nil)) ; ArrayIndexOfBounds exception
   (long-fix (ash this (- n))))
  ///
  (fty::deffixequiv Natural.shiftRight)
  (defrule Natural.shiftRight-when-nonnegative
    (implies (<= 0 (acl2::sbyte32-fix n))
             (equal (Natural.shiftRight this n)
                    (let* ((this (nfix this))
                           (n (acl2::sbyte32-fix n)))
                      (long-fix (fl (* this (expt 2 (- n))))))))
    :enable fl))

(acl2::with-arith5-help (define Natural.addShiftLeft
   ((this natp)
    (y natp)
    (n acl2::sbyte32p))
   :returns (result natp :rule-classes :type-prescription)
   (acl2::b*
   ((this (nfix this))
    (y (nfix y))
    (n (acl2::sbyte32-fix n))
    (n (acl2::loghead 6 n)))
   (+ this (ash y n)))
   ///
   (fty::deffixequiv Natural.addShiftLeft)))

(define Natural.divide
  ((this natp)
   (y natp))
  :returns (result-or-exception (implies result-or-exception
                                         (acl2::sbyte64p
                                          result-or-exception)))
  (acl2::b*
   ((this (nfix this))
    (y (nfix y))
    ((when (= y 0)) nil)) ; ArrayOutOfBounds
   (long-fix (fl (/ this y))))
  ///
  (fty::deffixequiv Natural.divide))

;; ACL2 models of math.Powers

(defconst *Powers.MAX_POW_5_EXP* 27)

(defconst *Powers.MAX_POW_5* #u7_450_580_596_923_828_125)

(defconst *Powers.MAX_POW_10_EXP* 19)

(defconst *Powers.MAX_POW_5_N_EXP* 340)

(acl2::with-arith5-help (define gen-powers
   ((b integerp)
    (n natp))
   :returns (powers acl2::sbyte64-listp)
   (and (posp n)
        (append
         (gen-powers b (1- n))
         (list (long-fix (expt (ifix b) (1- n))))))
   ///
   (fty::deffixequiv gen-powers)))

(defconst *Powers.pow5*
  (gen-powers 5 (+ *Powers.MAX_POW_5_EXP* 1)))

(defruled nth-pow5-when-i<=MAX_POW_5_EXP
  (implies (and (natp i)
                (< i (len *Powers.pow5*)))
           (equal (nth i *Powers.pow5*)
                  (expt 5 i)))
  :cases ((= i 0) (= i 1) (= i 2) (= i 3) (= i 4)
          (= i 5) (= i 6) (= i 7) (= i 8) (= i 9)
          (= i 10) (= i 11) (= i 12) (= i 13) (= i 14)
          (= i 15) (= i 16) (= i 17) (= i 18) (= i 19)
          (= i 20) (= i 21) (= i 22) (= i 23) (= i 24)
          (= i 25) (= i 26) (= i 27)))

(define Powers.pow5[]
  ((i acl2::sbyte32p))
  :returns (result-or-exception (implies result-or-exception
                                         (acl2::sbyte64p result-or-exception))
                                :hints (("goal" :use nth-pow5-when-i<=MAX_POW_5_EXP)))
  (acl2::b*
   ((i (acl2::sbyte32-fix i)))
   (and (natp i) (< i (len *Powers.pow5*)) (nth i *Powers.pow5*)))
  ///
  (fty::deffixequiv Powers.pow5[])
  (defrule Powers.pow5[]-type
    (or (null (Powers.pow5[] i))
        (natp (Powers.pow5[] i)))
    :rule-classes :type-prescription
    :use (:instance nth-pow5-when-i<=MAX_POW_5_EXP
                    (i (acl2::sbyte32-fix i))))
  (defruled Powers.pow5[]-when-i<=MAX_POW_5_EXP
    (implies (and (natp i)
                  (<= i *Powers.MAX_POW_5_EXP*))
             (equal (Powers.pow5[] i)
                    (expt 5 i)))
    :enable acl2::sbyte32p
    :use nth-pow5-when-i<=MAX_POW_5_EXP))

(defconst *Powers.pow10*
  (gen-powers 10 (+ *Powers.MAX_POW_10_EXP* 1)))

(defruled nth-pow10-when-i<=MAX_POW_10_EXP
  (implies (and (natp i)
                (< i (len *Powers.pow10*)))
           (equal (nth i *Powers.pow10*)
                  (long-fix (expt 10 i))))
  :cases ((= i 0) (= i 1) (= i 2) (= i 3) (= i 4)
          (= i 5) (= i 6) (= i 7) (= i 8) (= i 9)
          (= i 10) (= i 11) (= i 12) (= i 13) (= i 14)
          (= i 15) (= i 16) (= i 17) (= i 18) (= i 19)))

(define Powers.pow10[]
  ((i acl2::sbyte32p))
  :returns (result-or-exception (implies result-or-exception
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
                    (long-fix (expt 10 i))))
    :enable acl2::sbyte32p
    :use (:instance nth-pow10-when-i<=MAX_POW_10_EXP))
  (defruled Powers.pow10[]-when-i<MAX_POW_10_EXP
    (implies (and (natp i)
                  (< i *Powers.MAX_POW_10_EXP*))
             (equal (Powers.pow10[] i)
                    (expt 10 i)))
    :use (:instance nth-pow10-when-i<=MAX_POW_10_EXP)
    :cases ((= i 0) (= i 1) (= i 2) (= i 3) (= i 4)
            (= i 5) (= i 6) (= i 7) (= i 8) (= i 9)
            (= i 10) (= i 11) (= i 12) (= i 13) (= i 14)
            (= i 15) (= i 16) (= i 17) (= i 18))))

(acl2::with-arith5-help
 (define Powers.pow5
   ((i acl2::sbyte32p))
   :returns (result-or-exception (or (null result-or-exception)
                                     (natp result-or-exception))
                                 :rule-classes :type-prescription
                                 :hints (("goal" :use nth-pow10-when-i<=MAX_POW_10_EXP)))
   (acl2::b*
    ((i (acl2::sbyte32-fix i)))
    (and (natp i) (<= i *Powers.MAX_POW_5_N_EXP*) (expt 5 i)))
   ///
   (fty::deffixequiv Powers.pow5)
   (defrule Powers.pow5-type
     (or (null (Powers.pow5 i))
         (natp (Powers.pow5 i)))
     :rule-classes :type-prescription)))

;; ACL2 models of math.DoubleToDecimal

(fty::defprod DoubleToDecimal
  ((e acl2::sbyte32p)
   (q acl2::sbyte32p)
   (c acl2::sbyte64p)
   (lout acl2::sbyte32p)
   (rout acl2::sbyte32p)
   (buf character-listp)
   (index acl2::sbyte32p)))

(defconst *H* 17)

(defconst *G* 15)

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
   (* f (expt 10 (- e *H*))))
  ///
  (fty::deffixequiv DoubleToDecimal.toChars))

(local
 (acl2::with-arith5-help
  (defrule loop-measure-decreases
    (implies (and (acl2::sbyte32p g)
                  (<= 0 g))
             (< (int-fix (+ -1 g)) g))
    :enable int-fix)))

(acl2::with-arith5-help
 (define DoubleToDecimal.fullCaseXS-loop
  ((this DoubleToDecimal-p)
   (vb natp)
   (vbl natp)
   (vbr natp)
   (p acl2::sbyte32p)
   (sbH acl2::sbyte64p)
   (g acl2::sbyte32p))
  :measure (nfix (+ (acl2::sbyte32-fix g) 1))
  :returns (result-or-exception (or (not result-or-exception)
                                    (rationalp result-or-exception))
                                :rule-classes :type-prescription)
  (acl2::b*
   (((DoubleToDecimal this) (DoubleToDecimal-fix this))
    (vb (nfix vb))
    (vbl (nfix vbl))
    (vbr (nfix vbr))
    (p (acl2::sbyte32-fix p))
    (sbH (acl2::sbyte64-fix sbH))
    (g (acl2::sbyte32-fix g))

    ((unless (>= g 0)) nil) ; AssertionError
    (di (Powers.pow10[] g))
    ((unless di) nil) ; ArrayIndexOutOfBounds
    ((when (= di 0)) nil) ; DivideByZeroError
    (sbi (long-fix (- sbH (lrem sbH di))))
    (ubi (Natural.valueOfShiftLeft sbi p))
    ((unless ubi) nil)
    (wbi (Natural.valueOfShiftLeft (long-fix (+ sbi di)) p))
    ((unless wbi) nil)
    (uin (<= (int-fix (+ (Natural.compareTo vbl ubi) this.lout)) 0))
    (win (<= (int-fix (+ (Natural.compareTo wbi vbr) this.rout)) 0))
    ((when (and uin (not win)))
     (DoubleToDecimal.toChars this sbi this.e))
    ((when (and (not uin) win))
     (DoubleToDecimal.toChars this (long-fix (+ sbi di)) this.e))
    ((when uin)
     (let ((cmp (Natural.closerTo vb ubi wbi)))
       (if (or (< cmp 0)
               (and (= cmp 0)
                    ; di=0 was checked before
                    (= (long-fix (logand (ldiv sbi di) 1)) 0)))
           (DoubleToDecimal.toChars this sbi this.e)
         (DoubleToDecimal.toChars this (long-fix (+ sbi di)) this.e))))
    (g (int-fix (- g 1))))
   (DoubleToDecimal.fullCaseXS-loop this vb vbl vbr p sbH g))
  ///
  (encapsulate ()
    (local (in-theory
            '(DoubleToDecimal.fullCaseXS-loop
              (:CONGRUENCE DOUBLETODECIMAL-EQUIV-IMPLIES-EQUAL-DOUBLETODECIMAL-FIX-1)
              (:CONGRUENCE ACL2::NAT-EQUIV-IMPLIES-EQUAL-NFIX-1)
              (:CONGRUENCE ACL2::SBYTE64-EQUIV-IMPLIES-EQUAL-SBYTE64-FIX-1)
              (:CONGRUENCE ACL2::SBYTE32-EQUIV-IMPLIES-EQUAL-SBYTE32-FIX-1)
              DOUBLETODECIMAL-FIX-UNDER-DOUBLETODECIMAL-EQUIV
              ACL2::NFIX-UNDER-NAT-EQUIV
              ACL2::SBYTE64-FIX-UNDER-SBYTE64-EQUIV
              ACL2::SBYTE32-FIX-UNDER-SBYTE32-EQUIV)))
    (fty::deffixequiv DoubleToDecimal.fullCaseXS-loop))))

(define DoubleToDecimal.fullCaseXS
  ((this DoubleToDecimal-p)
   (qb acl2::sbyte32p)
   (cb acl2::sbyte64p)
   (cb_r acl2::sbyte64p)
   (i acl2::sbyte32p))
  :returns (result-or-exception (or (not result-or-exception)
                                    (rationalp result-or-exception))
                                :rule-classes :type-prescription)
  (acl2::b*
   (((DoubleToDecimal this) this)
    (qb (acl2::sbyte32-fix qb))
    (cb (acl2::sbyte64-fix cb))
    (cb_r (acl2::sbyte64-fix cb_r))
    (i (acl2::sbyte32-fix i))
    (m (Powers.pow5 (int-fix (- *H* this.e))))
    ((unless m) nil)
    (vb (Natural.multiply m cb))
    (vbl (Natural.subtract vb m))
    ((unless vbl) nil)
    (vbr (Natural.multiply m cb_r))
    (p (int-fix (- (int-fix (- this.e *H*)) qb)))
    (sbH (Natural.shiftRight vb p))
    ((unless sbH) nil)
    (g (int-fix (- *H* i))))
   (DoubleToDecimal.fullCaseXS-loop this vb vbl vbr p sbH g))
  ///
  (fty::deffixequiv DoubleToDecimal.fullCaseXS))

(acl2::with-arith5-help (define DoubleToDecimal.fullCaseXL-loop
  ((this DoubleToDecimal-p)
   (qb acl2::sbyte32p)
   (vb natp)
   (vbl natp)
   (vbr natp)
   (m natp)
   (sbH acl2::sbyte64p)
   (g acl2::sbyte32p))
  :measure (nfix (+ (acl2::sbyte32-fix g) 1))
  :returns (result-or-exception (or (not result-or-exception)
                                    (rationalp result-or-exception))
                                :rule-classes :type-prescription)
  (acl2::b*
   (((DoubleToDecimal this) (DoubleToDecimal-fix this))
    (qb (acl2::sbyte32-fix qb))
    (vb (nfix vb))
    (vbl (nfix vbl))
    (vbr (nfix vbr))
    (m (nfix m))
    (sbH (acl2::sbyte64-fix sbH))
    (g (acl2::sbyte32-fix g))

    ((unless (>= g 0)) nil) ; AssertionError
    (di (Powers.pow10[] g))
    ((unless di) nil) ; ArrayIndexOutOfBounds
    ((when (= di 0)) nil) ; DivideByZeroError
    (sbi (long-fix (- sbH (lrem sbH di))))
    (ubi (Natural.multiply m sbi))
    ((unless ubi) nil)
    (pow5 (Powers.pow5 (int-fix (+ (int-fix (- this.e *H*)) g))))
    ((unless pow5) nil)
    (wbi (Natural.addShiftLeft ubi pow5 g))
    (uin (<= (int-fix (+ (Natural.compareTo vbl ubi) this.lout)) 0))
    (win (<= (int-fix (+ (Natural.compareTo wbi vbr) this.rout)) 0))
    ((when (and uin (not win)))
     (DoubleToDecimal.toChars this sbi this.e))
    ((when (and (not uin) win))
     (DoubleToDecimal.toChars this (long-fix (+ sbi di)) this.e))
    ((when uin)
     (let ((cmp (Natural.closerTo vb ubi wbi)))
       (if (or (< cmp 0)
               (and (= cmp 0)
                    ; di=0 was checked before
                    (= (long-fix (logand (ldiv sbi di) 1)) 0)))
           (DoubleToDecimal.toChars this sbi this.e)
         (DoubleToDecimal.toChars this (long-fix (+ sbi di)) this.e))))
    (g (int-fix (- g 1))))
   (DoubleToDecimal.fullCaseXL-loop this qb vb vbl vbr m sbH g))
  ///
  (encapsulate ()
    (local (in-theory
            '(DoubleToDecimal.fullCaseXL-loop
              (:CONGRUENCE DOUBLETODECIMAL-EQUIV-IMPLIES-EQUAL-DOUBLETODECIMAL-FIX-1)
              (:CONGRUENCE ACL2::NAT-EQUIV-IMPLIES-EQUAL-NFIX-1)
              (:CONGRUENCE ACL2::SBYTE64-EQUIV-IMPLIES-EQUAL-SBYTE64-FIX-1)
              (:CONGRUENCE ACL2::SBYTE32-EQUIV-IMPLIES-EQUAL-SBYTE32-FIX-1)
              DOUBLETODECIMAL-FIX-UNDER-DOUBLETODECIMAL-EQUIV
              ACL2::NFIX-UNDER-NAT-EQUIV
              ACL2::SBYTE64-FIX-UNDER-SBYTE64-EQUIV
              ACL2::SBYTE32-FIX-UNDER-SBYTE32-EQUIV)))
    (fty::deffixequiv DoubleToDecimal.fullCaseXL-loop))))

(define DoubleToDecimal.fullCaseXL
  ((this DoubleToDecimal-p)
   (qb acl2::sbyte32p)
   (cb acl2::sbyte64p)
   (cb_r acl2::sbyte64p))
  :returns (result-or-exception (or (not result-or-exception)
                                    (rationalp result-or-exception))
                                :rule-classes :type-prescription)
  (acl2::b*
   (((DoubleToDecimal this) this)
    (qb (acl2::sbyte32-fix qb))
    (cb (acl2::sbyte64-fix cb))
    (cb_r (acl2::sbyte64-fix cb_r))
    (p (int-fix (+ (int-fix (- *H* this.e)) qb)))
    (vb (Natural.valueOfShiftLeft cb p))
    ((unless vb) nil)
    (vbl (Natural.valueOfShiftLeft (long-fix (- cb 1)) p))
    ((unless vbl) nil)
    (vbr (Natural.valueOfShiftLeft cb_r p))
    ((unless vbr) nil)
    (m (Powers.pow5 p))
    ((unless m) nil)
    (sbH (Natural.shiftRight vb p))
    ((unless sbH) nil)
    (g (int-fix (- *H* *G*))))
   (DoubleToDecimal.fullCaseXL-loop this qb vb vbl vbr m sbH g))
  ///
  (fty::deffixequiv DoubleToDecimal.fullCaseXL))
