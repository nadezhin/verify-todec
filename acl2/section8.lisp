(in-package "RTL")
(include-book "section7")

;(local (include-book "rtl/rel11/support/basic" :dir :system))
(local (include-book "rtl/rel11/support/float" :dir :system))
(local (acl2::allow-arith5-help))

(define k
  ((v pos-rationalp)
   (f formatp))
  :returns (k integerp :rule-classes ())
  (expe (wid-Rv v f) (D))
  ///
  (fty::deffixequiv k))

(defrule result-6-k
  (acl2::b*
   ((Rv (Rv v f))
    (k (k v f)))
   (implies (finite-positive-binary-p v f)
            (or (in-tau-intervalp (u_i v k) Rv)
                (in-tau-intervalp (w_i v k) Rv))))
  :rule-classes ()
  :enable (k expe-lower-bound)
  :use (:instance result-5
                  (i (k v f))))

(acl2::with-arith5-help
 (rule
  (and (D_i-p (u_i v k) k)
       (D_i-p (w_i v k) k))
  :enable (D_i-p u_i w_i)))

(acl2::with-arith5-help
 (defrule result-6-k+1
  (acl2::b*
   ((Rv (Rv v f))
    (k+1 (+ (k v f) 1)))
   (implies (and (in-tau-intervalp y Rv)
                 (D_i-p x k+1)
                 (D_i-p y k+1)
                 (not (= x y)))
            (not (in-tau-intervalp x Rv))))
  :use (:instance result-4
                  (i (1+ (k v f)))
                  (d1 (* y (expt (D) (- (1+ (k v f))))))
                  (d2 (* x (expt (D) (- (1+ (k v f)))))))
  :enable (k D_i-p D-value expe-upper-bound)))

(acl2::with-arith5-nonlinear-help
 (defrule result-7-u
  (acl2::b*
   ((k (k v f)))
   (implies (and (D_i-p x k)
                 (< x (pos-rational-fix v))
                 (not (= x (u_i v k))))
            (< x (u_i v k))))
  :enable (D_i-p u_i s_i t_i)
  :cases ((not (integerp (* x (expt (D) (- (k v f))))))
          (<= (* x (expt (D) (- (k v f)))) (s_i v (k v f)))
          (>= (* x (expt (D) (- (k v f)))) (t_i v (k v f))))))

(acl2::with-arith5-nonlinear-help
 (defrule result-7-w
  (acl2::b*
   ((k (k v f)))
   (implies (and (D_i-p x k)
                 (> x (pos-rational-fix v))
                 (not (= x (w_i v k))))
            (> x (w_i v k))))
  :enable (D_i-p w_i s_i t_i)
  :cases ((not (integerp (* x (expt (D) (- (k v f))))))
          (<= (* x (expt (D) (- (k v f)))) (s_i v (k v f)))
          (>= (* x (expt (D) (- (k v f)))) (t_i v (k v f))))))


