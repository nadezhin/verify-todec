;; Support for ACL2 models of Java code
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

(define i2l
  ((x acl2::sbyte32p))
  :returns (result acl2::sbyte64p)
  (acl2::b*
   ((x (acl2::sbyte32-fix x)))
   (long-fix x))
  ///
  (fty::deffixequiv i2l))

(define iadd
  ((x acl2::sbyte32p)
   (y acl2::sbyte32p))
  :returns (result acl2::sbyte32p)
  (acl2::b*
   ((x (acl2::sbyte32-fix x))
    (y (acl2::sbyte32-fix y)))
   (int-fix (+ x y)))
  ///
  (fty::deffixequiv iadd))

(define iand
  ((x acl2::sbyte32p)
   (y acl2::sbyte32p))
  :returns (result acl2::sbyte32p)
  (acl2::b*
   ((x (acl2::sbyte32-fix x))
    (y (acl2::sbyte32-fix y)))
   (int-fix (logand x y)))
  ///
  (fty::deffixequiv iand))

(define if_icmpge
  ((x acl2::sbyte32p)
   (y acl2::sbyte32p))
  :returns (continue booleanp :rule-classes ())
  (acl2::b*
   ((x (acl2::sbyte32-fix x))
    (y (acl2::sbyte32-fix y))
    (jmp (>= x y)))
   (not jmp))
  ///
  (fty::deffixequiv if_icmpge))

(define if_icmpne
  ((x acl2::sbyte32p)
   (y acl2::sbyte32p))
  :returns (continue booleanp :rule-classes ())
  (acl2::b*
   ((x (acl2::sbyte32-fix x))
    (y (acl2::sbyte32-fix y))
    (jmp (not (= x y))))
   (not jmp))
  ///
  (fty::deffixequiv if_icmpne))

(define ifeq
  ((x acl2::sbyte32p))
  :returns (continue booleanp :rule-classes ())
  (acl2::b*
   ((x (acl2::sbyte32-fix x))
    (jmp (= x 0)))
   (not jmp))
  ///
  (fty::deffixequiv ifeq))

(define ifle
  ((x acl2::sbyte32p))
  :returns (continue booleanp :rule-classes ())
  (acl2::b*
   ((x (acl2::sbyte32-fix x))
    (jmp (<= x 0)))
   (not jmp))
  ///
  (fty::deffixequiv ifle))

(define ifne
  ((x acl2::sbyte32p))
  :returns (continue booleanp :rule-classes ())
  (acl2::b*
   ((x (acl2::sbyte32-fix x))
    (jmp (not (= x 0))))
   (not jmp))
  ///
  (fty::deffixequiv ifne))

(define ior
  ((x acl2::sbyte32p)
   (y acl2::sbyte32p))
  :returns (result acl2::sbyte32p)
  (acl2::b*
   ((x (acl2::sbyte32-fix x))
    (y (acl2::sbyte32-fix y)))
   (int-fix (logior x y)))
  ///
  (fty::deffixequiv ior))

(define ishl
  ((x acl2::sbyte32p)
   (y acl2::sbyte32p))
  :returns (results acl2::sbyte32p)
  (acl2::b*
   ((x (acl2::sbyte32-fix x))
    (y (acl2::sbyte32-fix y))
    (n (acl2::loghead 5 y)))
   (int-fix (ash x n)))
  ///
  (fty::deffixequiv ishl))

(define isub
  ((x acl2::sbyte32p)
   (y acl2::sbyte32p))
  :returns (result acl2::sbyte32p)
  (acl2::b*
   ((x (acl2::sbyte32-fix x))
    (y (acl2::sbyte32-fix y)))
   (int-fix (- x y)))
  ///
  (fty::deffixequiv isub))

(define l2i
  ((x acl2::sbyte64p))
  :returns (result acl2::sbyte32p)
  (acl2::b*
   ((x (acl2::sbyte64-fix x)))
   (int-fix x))
  ///
  (fty::deffixequiv l2i))

(define ladd
  ((x acl2::sbyte64p)
   (y acl2::sbyte64p))
  :returns (result acl2::sbyte64p)
  (acl2::b*
   ((x (acl2::sbyte64-fix x))
    (y (acl2::sbyte64-fix y)))
   (long-fix (+ x y)))
  ///
  (fty::deffixequiv ladd))

(define land
  ((x acl2::sbyte64p)
   (y acl2::sbyte64p))
  :returns (result acl2::sbyte64p)
  (acl2::b*
   ((x (acl2::sbyte64-fix x))
    (y (acl2::sbyte64-fix y)))
   (long-fix (logand x y)))
  ///
  (fty::deffixequiv land))

(define lcmp
  ((x acl2::sbyte64p)
   (y acl2::sbyte64p))
  :returns (result acl2::sbyte32p)
  (acl2::b*
   ((x (acl2::sbyte64-fix x))
    (y (acl2::sbyte64-fix y)))
   (signum (- x y)))
  ///
  (fty::deffixequiv lcmp))

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

(define lmul
  ((x acl2::sbyte64p)
   (y acl2::sbyte64p))
  :returns (result acl2::sbyte64p)
  (acl2::b*
   ((x (acl2::sbyte64-fix x))
    (y (acl2::sbyte64-fix y)))
   (long-fix (* x y)))
  ///
  (fty::deffixequiv lmul))

(define lor
  ((x acl2::sbyte64p)
   (y acl2::sbyte64p))
  :returns (result acl2::sbyte64p)
  (acl2::b*
   ((x (acl2::sbyte64-fix x))
    (y (acl2::sbyte64-fix y)))
   (long-fix (logior x y)))
  ///
  (fty::deffixequiv lor))

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

(define lshr
  ((x acl2::sbyte64p)
   (y acl2::sbyte32p))
  :returns (results acl2::sbyte64p)
  (acl2::b*
   ((x (acl2::sbyte64-fix x))
    (y (acl2::sbyte32-fix y))
    (n (acl2::loghead 6 y)))
   (long-fix (ash x (- n))))
  ///
  (fty::deffixequiv lshr))

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

(define lushr
  ((x acl2::sbyte64p)
   (y acl2::sbyte32p))
  :returns (results acl2::sbyte64p)
  (acl2::b*
   ((x (acl2::sbyte64-fix x))
    (y (acl2::sbyte32-fix y))
    (xu (acl2::loghead 64 x))
    (n (acl2::loghead 6 y)))
   (long-fix (ash xu (- n))))
  ///
  (fty::deffixequiv lushr))

