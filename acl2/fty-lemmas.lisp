(in-package "RTL")
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "rtl/rel11/support/verify-guards" :dir :system)

(fty::deffixtype real
  :pred real/rationalp
  :fix realfix
  :equiv real-equiv
  :define t)

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
  (defrule pos-rational-fix-when-pos-rationalp
    (implies (pos-rationalp x)
             (equal (pos-rational-fix x) x)))
  (fty::deffixtype pos-rational
    :pred pos-rationalp
    :fix pos-rational-fix
    :equiv pos-rational-equiv
    :define t)
  (in-theory (disable pos-rational-equiv)))

(defrule radixp-compound-recognizer
  (equal (radixp b)
         (and (integerp b) (< 1 b)))
  :rule-classes :compound-recognizer
  :enable radixp)

(define radix-fix
  ((b radixp))
  :returns (b-fixed radixp :rule-classes ())
  (if (radixp b) b 2)
  ///
  (defrule radix-fix-when-radixp
    (implies (radixp x)
             (equal (radix-fix x) x)))
  (fty::deffixtype radix
    :pred radixp
    :fix radix-fix
    :equiv radix-equiv
    :define t)
  (in-theory (disable radix-equiv)))

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
(in-theory (disable format-equiv))
