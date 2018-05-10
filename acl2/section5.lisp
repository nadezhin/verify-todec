(in-package "RTL")
(include-book "section4")

(local (include-book "rtl/rel11/support/float" :dir :system))
(local (acl2::allow-arith5-help))

(define has-D-length
  ((x pos-rationalp)
   (i natp)
   (D radixp))
  :returns (yes booleanp :rule-classes ())
  (let ((x (pos-rational-fix x))
        (i (nfix i))
        (D (radix-fix D)))
    (exactrp x i D))
  ///
  (fty::deffixequiv has-D-length))

(defruled has-D-length-monotone
  (implies (and (has-D-length x i D)
                (<= (nfix i) (nfix j)))
           (has-D-length x j D))
  :enable (has-D-length exactrp-<=))

(define e
  ((x pos-rationalp)
   (D radixp))
  :returns (e integerp :rule-classes ())
  (ordD D x)
  ///
  (fty::deffixequiv e)
  (defruled e-as-expe
    (equal (e x D)
           (+ (expe (pos-rational-fix x) (radix-fix D)) 1))
    :enable ordD))

(acl2::with-arith5-help
 (define f
   ((x pos-rationalp)
    (D radixp))
   :returns (f pos-rationalp
               :rule-classes :type-prescription
               :hints (("goal" :in-theory (enable pos-rational-fix
                                                  pos-rationalp))))
   (* (pos-rational-fix x) (expt (radix-fix D) (- (e x D))))
   ///
   (fty::deffixequiv f)
   (defruled f-as-sigm
     (equal (f x D)
            (let ((x (pos-rational-fix x))
                  (D (radix-fix D)))
              (/ (sigm x D) D)))
     :enable (pos-rational-fix sigm e-as-expe))))

(acl2::with-arith5-help
 (defrule f-linear
   (and (<= (/ (radix-fix D)) (f x D))
        (< (f x D) 1))
   :rule-classes :linear
   :enable (pos-rational-fix radix-fix f-as-sigm)
   :use ((:instance sigm-lower-bound
                    (b (radix-fix D))
                    (x (pos-rational-fix x)))
         (:instance sigm-upper-bound
                    (b (radix-fix D))
                      (x (pos-rational-fix x))))))

(defrule ordD-f
  (equal (ordD D (f x D)) 0)
  :enable pos-rational-fix
  :use (:instance result-1-3 (k 0) (x (f x D))))
