(in-package "RTL")
(include-book "section4")

(local (include-book "rtl/rel11/support/float" :dir :system))
(local (acl2::allow-arith5-help))

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
     :enable (sigm e-as-expe))))

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
  :use (:instance result-1-3 (k 0) (x (f x D))))

; Use result-2 statement as definition in proof script
(define has-D-length
  ((x pos-rationalp)
   (i posp)
   (D radixp))
  :returns (yes booleanp :rule-classes ())
  (let ((x (pos-rational-fix x))
        (i (acl2::pos-fix i))
        (D (radix-fix D)))
    (integerp (* (f x D) (expt D i))))
  ///
  (fty::deffixequiv has-D-length)
  (acl2::with-arith5-help
   (defruled has-D-length-as-exactrp
     (equal (has-D-length x i D)
            (exactrp (pos-rational-fix x) (acl2::pos-fix i) (radix-fix D)))
     :enable (f-as-sigm exactrp sigc)))
  (acl2::with-arith5-help
   (defruled has-D-length-necc ; part of result-2
     (implies (has-D-length x i D)
              (let* ((x (pos-rational-fix x))
                     (i (acl2::pos-fix i))
                     (D (radix-fix D))
                     (r (- (e x D) i))
                     (d_ (* x (expt D (- r)))))
                (and (integerp r)
                     (integerp d_)
                     (equal (ordD D d_) i))))
     :enable (result-1-5 e f)))
  (acl2::with-arith5-help
   (defrule has-D-length-suff ; part of result-2
     (implies (and (radixp D)
                   (integerp r)
                   (posp d_))
              (let ((x (* d_ (expt D r)))
                    (i (ordD D d_)))
                (has-D-length x i D)))
     :enable (f e result-1-5)
     :use ((:instance result-1-4 (x 1) (y d_))
           (:instance result-1-3 (x 1) (k 1))))))

(defruled has-D-length-monotone
  (implies (and (has-D-length x i D)
                (<= (acl2::pos-fix i) (acl2::pos-fix j)))
           (has-D-length x j D))
  :enable (has-D-length-as-exactrp exactrp-<=))
