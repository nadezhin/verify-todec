(in-package "RTL")
(include-book "fty-lemmas")

(local (acl2::allow-arith5-help))

(define D/2 ()
  5
  :returns (D/2 radixp :rule-classes :type-prescription)
  ///
  (defruled evenp-expt-D/2-1
    (implies (natp i)
             (evenp (- (expt (D/2) i) 1)))
    :disable evenp
    :prep-lemmas
    ((acl2::with-arith5-nonlinear-help
      (defrule lemma
        (implies (evenp (1- k))
                 (evenp (1- (* 5 k))))
        :cases ((integerp k))
        :disable acl2::even-and-odd-alternate
        :hints (("subgoal 2" :in-theory
                 (enable acl2::even-and-odd-alternate)))))))
  (in-theory (disable (:executable-counterpart D/2))))

(defrule expt-D/2-type
  (pos-rationalp (expt (D/2) k))
  :rule-classes :type-prescription)

(defrule expt-D/2-type-when-natp-k
  (implies (natp k)
           (posp (expt (D/2) k)))
  :rule-classes :type-prescription)

(defrule int-equiv-implies-equal-expt-D/2-2
  (implies (acl2::int-equiv k k-equiv)
           (equal (expt (D/2) k)
                  (expt (D/2) k-equiv)))
  :rule-classes :congruence)

(acl2::with-arith5-help
 (defruled oddp-expt-D/2
   (oddp (expt (D/2) i))
   :cases ((< (ifix i) 0) (>= (ifix i) 0))
   :hints (("subgoal 2" :cases ((< (expt (D/2) i) 1)))
           ("subgoal 1" :use evenp-expt-D/2-1))))

(acl2::with-arith5-help
 (defruled powers-of-2-and-D/2-are-distinct
 (implies (= (expt 2 i) (expt (D/2) j))
          (and (zip i) (zip j)))
 :cases ((and (integerp i) (< i 0))
         (and (integerp i) (> i 0)))
 :hints (("subgoal 2" :in-theory (disable lemma)
          :use (:instance lemma
                          (i (- i))
                          (j (- (ifix j))))))
 :prep-lemmas
 ((defrule lemma
    (implies (posp i)
             (not (equal (expt 2 i) (expt (D/2) j))))
    :use (:instance oddp-expt-D/2 (i j))))))

(define D ()
  (* 2 (D/2))
  :returns (D radixp)
  ///
  (defrule D/2-type
    (and (integerp (* 1/2 (D)))
         (< 1 (* 1/2 (D))))
    :rule-classes :type-prescription)
  (in-theory (disable (:executable-counterpart D)))
  (acl2::with-arith5-help
   (defruled expt-D-as-expt-D/2
     (equal (expt (D) k)
            (* (expt 2 k) (expt (D/2) k))))))

(defrule expt-D-type
  (pos-rationalp (expt (D) k))
  :rule-classes :type-prescription)

(defrule expt-D-type-when-natp-k
  (implies (natp k)
           (posp (expt (D) k)))
  :rule-classes :type-prescription)

(defrule int-equiv-implies-equal-expt-D-2
  (implies (acl2::int-equiv k k-equiv)
           (equal (expt (D) k)
                  (expt (D) k-equiv)))
  :rule-classes :congruence)

(acl2::with-arith5-nonlinear-help
 (defruled powers-of-2-and-D-are-distinct
   (implies (= (expt 2 i) (expt (D) j))
            (and (zip i) (zip j)))
   :enable D
   :use (:instance powers-of-2-and-D/2-are-distinct
                   (i (- (ifix i) (ifix j))))))

(rule
 (equal (rne #f1.2 (prec (dp)))
        #f1.1999999999999999555910790149937383830547332763671875)
 :enable dp)
