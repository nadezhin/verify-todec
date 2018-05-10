(in-package "RTL")
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "rtl/rel11/support/verify-guards" :dir :system)

(define radix-fix
  ((b radixp))
  :returns (b radixp)
  (if (radixp b) b 2)
  ///
  (defrule radix-fix-when-radixp
    (implies (radixp b)
             (equal (radix-fix b) b)))
  (fty::deffixtype radix
    :pred radixp
    :fix radix-fix
    :equiv radix-equiv
    :define t))

(fty::deffixtype real
  :pred real/rationalp
  :fix realfix
  :equiv real-equiv
  :define t)

#|
           6:x(FTY::DEFFIXTYPE REAL :PRED ...)
 v             (ENCAPSULATE NIL ...)
                (DEFMACRO REAL-EQUIV (X Y) ...)
                (TABLE ACL2::MACRO-ALIASES-TABLE 'REAL-EQUIV
                       ...)
                (TABLE UNTRANS-TABLE 'REAL-EQUIV$INLINE
                       ...)
 V              (DEFUN REAL-EQUIV$INLINE (X Y) ...)
                (DEFTHM REAL-EQUIV-IS-AN-EQUIVALENCE ...)
                (DEFTHM REAL-EQUIV-IMPLIES-EQUAL-REALFIX-1 ...)
                (DEFTHM REALFIX-UNDER-REAL-EQUIV ...)
                (TABLE FTY::FIXTYPES 'FTY::FIXTYPE-ALIST
                       ...)

|#

(define pos-rationalp
  ((x t))
  :returns (yes booleanp :rule-classes nil)
  (and (rationalp x) (< 0 x))
  ///
  (defrule pos-rationalp-compound-recognizer
    (equal (pos-rationalp x)
           (and (rationalp x) (< 0 x)))
    :rule-classes :compound-recognizer))

(define pos-rational-fix
  ((x pos-rationalp))
  :returns (x pos-rationalp)
  (if (pos-rationalp x) x 1)
  ///
  (fty::deffixtype pos-rational
    :pred pos-rationalp
    :fix pos-rational-fix
    :equiv pos-rational-equiv
    :define t))

(define format-fix
  ((f formatp))
  :returns (f formatp
              :hints (("goal" :in-theory (enable formatp))))
  (let ((explicitp (explicitp f))
        (prec (prec f))
        (expw (expw f)))
    (list*
     explicitp
     (if (and (integerp prec) (> prec 1)) prec 2)
     (if (and (integerp expw) (> expw 1)) expw 2)
     (cdddr f)))
  :guard-hints (("goal" :in-theory (enable formatp)))
  ///
  (defrule format-fix-when-formatp
    (implies (formatp f)
             (equal (format-fix f) f))
    :enable (formatp explicitp prec expw)))

(fty::deffixtype format
    :pred formatp
    :fix format-fix
    :equiv format-equiv
    :define t)
