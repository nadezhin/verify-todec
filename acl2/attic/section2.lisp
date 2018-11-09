(in-package "RTL")
(include-book "../fty-lemmas")

(local (include-book "rtl/rel11/support/float" :dir :system))
(local (acl2::allow-arith5-help))

; Section 2 of the paper

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

(define ord2
  ((x pos-rationalp))
  :returns (ord2 integerp :rule-classes ())
  (let ((x (pos-rational-fix x)))
    (1+ (expe x 2)))
  ///
  (fty::deffixequiv ord2))

(define ordD
  ((x pos-rationalp))
  :returns (ordD integerp :rule-classes ())
  (let ((x (pos-rational-fix x)))
    (1+ (expe x (D))))
  ///
  (fty::deffixequiv ordD))

(acl2::with-arith5-help
 (defrule result-1-1
   (implies (and (real/rationalp x)
                 (integerp m)
                 (integerp n))
            (equal (and (<= m x) (< x n))
                   (and (<= m (fl x)) (< (fl x) n))))
   :rule-classes ()))

(defrule result-1-2
  (implies (and (real/rationalp x)
                (integerp m)
                (integerp n))
           (equal (and (< m x) (<= x n))
                  (and (< m (cg x)) (<= (cg x) n))))
  :rule-classes ())

(defrule result-1-3
  (equal (= k (ordD x))
         (let ((x (pos-rational-fix x)))
           (and (integerp k)
                (<= (expt (D) (- k 1)) x)
                (< x (expt (D) k)))))
  :rule-classes ()
  :enable (ordD expe-lower-bound expe-upper-bound)
  :cases ((= k (ordD x)))
  :use (:instance expe-unique
                  (b (D))
                  (x (pos-rational-fix x))
                  (n (1- k))))

(defrule result-1-3-ord2
  (equal (= k (ord2 x))
         (let ((x (pos-rational-fix x)))
           (and (integerp k)
                (<= (expt 2 (- k 1)) x)
                (< x (expt 2 k)))))
  :rule-classes ()
  :enable (ord2 expe-lower-bound expe-upper-bound)
  :cases ((= k (ord2 x)))
  :use (:instance expe-unique
                  (b 2)
                  (x (pos-rational-fix x))
                  (n (1- k))))

(defrule ordD-1
  (equal (ordD 1) 1)
  :use (:instance result-1-3 (x 1) (k 1)))

(acl2::with-arith5-help
 (defrule ordD-expt-D
   (implies (integerp k)
            (equal (ordD (expt (D) k)) (+ k 1)))
   :use (:instance result-1-3 (x (expt (D) k)) (k (+ k 1)))))

(defrule ordD-D
  (equal (ordD (D)) 2)
  :expand (expt (D) 1)
  :use (:instance ordD-expt-D (k 1)))

(defrule ordD-/D
  (equal (ordD (/ (D))) 0)
  :use (:instance ordD-expt-D (k -1)))

(defruled result-1-4
  (implies (< (pos-rational-fix x)
              (pos-rational-fix y))
           (<= (ordD x)
               (ordD y)))
  :enable ordD
  :use (:instance expe-monotone
                  (b (D))
                  (x (pos-rational-fix x))
                  (y (pos-rational-fix y))))

(acl2::with-arith5-help
 (defruled result-1-5
   (implies (and (pos-rationalp d)
                 (integerp r))
            (equal (ordD (* d (expt (D) r)))
                   (+ r (ordD d))))
   :enable ordD
   :use (:instance expe-shift (b (D)) (x d) (n r))))

(acl2::with-arith5-help
 (defruled result-1-6
  (implies (and (rationalp x)
                (<= 1 x))
           (equal (ordD (fl x)) (ordD x)))
  :enable (ordD pos-rationalp)
  :use ((:instance expe-unique (b (D)) (n (expe (fl x) (D))))
        (:instance expe-lower-bound (b (D)) (x (fl x)))
        (:instance expe-upper-bound (b (D)) (x (fl x)))
        (:instance result-1-1
                   (m (expt (D) (expe (fl x) (D))))
                   (n (expt (D) (1+ (expe (fl x) (D)))))))))
