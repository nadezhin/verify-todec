(in-package "RTL")
(include-book "section5")

(local (include-book "rtl/rel11/support/basic" :dir :system))
(local (acl2::allow-arith5-help))

; Definition 3

(define D_i-p
  ((x real/rationalp)
   (i integerp))
  :returns (belongs booleanp :rule-classes ())
  (acl2::b*
   ((x (realfix x))
    (i (ifix i)))
   (integerp (* x (expt (D) (- i)))))
  ///
  (fty::deffixequiv D_i-p))

(acl2::with-arith5-nonlinear++-help
 (defruled D_{i+1}
   (implies (D_i-p x (+ (ifix i) 1))
            (D_i-p x i))
   :enable (D_i-p (D))))

(define s_i
  ((v pos-rationalp)
   (i integerp))
  :returns (s_i natp :rule-classes :type-prescription)
  (acl2::b*
   ((v (pos-rational-fix v))
    (i (ifix i)))
   (fl (* v (expt (D) (- i)))))
  ///
  (fty::deffixequiv s_i))

(define t_i
  ((v pos-rationalp)
   (i integerp))
  :returns (t_i posp :rule-classes ())
  (+ (s_i v i) 1)
  ///
  (fty::deffixequiv t_i))

(define u_i
  ((v pos-rationalp)
   (i integerp))
  :returns (u_i (and (rationalp u_i) (<= 0 u_i)) :rule-classes ())
  (* (s_i v i) (expt (D) (ifix i)))
  ///
  (fty::deffixequiv u_i))

(define w_i
  ((v pos-rationalp)
   (i integerp))
  :returns (w_i pos-rationalp :rule-classes ())
  (* (t_i v i) (expt (D) (ifix i)))
  ///
  (fty::deffixequiv w_i))
