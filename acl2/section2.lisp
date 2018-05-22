(in-package "RTL")
(include-book "fty-lemmas")

(local (include-book "rtl/rel11/support/basic" :dir :system))
(local (include-book "rtl/rel11/support/float" :dir :system))
(local (acl2::allow-arith5-help))

; Section 2 of the paper

(define ordD
  ((d radixp)
   (x pos-rationalp))
  :returns (d integerp :rule-classes ())
  (let ((d (radix-fix d))
        (x (pos-rational-fix x)))
    (1+ (expe x d)))
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
  (equal (= k (ordD D x))
         (let ((x (pos-rational-fix x))
               (D (radix-fix D)))
           (and (integerp k)
                (<= (expt D (- k 1)) x)
                (< x (expt D k)))))
  :rule-classes ()
  :enable (ordD expe-lower-bound expe-upper-bound)
  :cases ((= k (ordD D x)))
  :use (:instance expe-unique
                  (b (radix-fix D))
                  (x (pos-rational-fix x))
                  (n (1- k))))

(defruled result-1-4
  (implies (< (pos-rational-fix x)
              (pos-rational-fix y))
           (<= (ordD D x)
               (ordD D y)))
  :enable ordD
  :use (:instance expe-monotone
                  (b (radix-fix D))
                  (x (pos-rational-fix x))
                  (y (pos-rational-fix y))))

(acl2::with-arith5-help
 (defruled result-1-5
   (implies (and (pos-rationalp d_)
                 (integerp r)
                 (radixp D))
            (equal (ordD D (* d_ (expt D r)))
                   (+ r (ordD D d_))))
   :enable ordD
   :use (:instance expe-shift (b D) (x d_) (n r))))

(defruled result-1-6
  (implies (and (rationalp x)
                (<= 1 x))
           (equal (ordD D (fl x)) (ordD D x)))
  :use (:instance lemma (d (radix-fix D)))
  :prep-lemmas
  ((acl2::with-arith5-help
    (defrule lemma
      (implies (and (rationalp x)
                    (<= 1 x)
                    (radixp D))
               (equal (ordD D (fl x)) (ordD D x)))
      :enable (ordD pos-rationalp)
      :use ((:instance expe-unique (b D) (n (expe (fl x) D)))
            (:instance expe-lower-bound (b D) (x (fl x)))
            (:instance expe-upper-bound (b D) (x (fl x)))
            (:instance result-1-1
                       (m (expt D (expe (fl x) D)))
                       (n (expt D (1+ (expe (fl x) D))))))))))
