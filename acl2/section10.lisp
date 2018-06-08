#|
(include-book "rtl/rel11/portcullis" :dir :system)
|#
(in-package "RTL")
(include-book "section9")

(local (include-book "rtl/rel11/support/float" :dir :system))
(local (include-book "std/basic/inductions" :dir :system))
(local (acl2::allow-arith5-help))

(acl2::with-arith5-nonlinear++-help
 (defruled 2^p-is-not-D^k
   (implies (posp p)
            (not (equal (expt 2 p) (expt (D) k))))
   :cases ((equal (expt 2 (- p (ifix k))) (expt 5 (ifix k)))
           (= p (ifix k)))
   :hints (("subgoal 3" :in-theory (enable D))
           ("subgoal 2" :use (:instance lemma5
                                        (i (- p (ifix k)))
                                        (j (ifix k))))
           ("subgoal 1" :use lemma6))
   :prep-lemmas
   ((acl2::with-arith5-help
     (defruled lemma1
       (implies (integerp k)
                (integerp (* 1/2 (- (* 5 (1+ (* 2 k))) 1))))))
    (acl2::with-arith5-help
     (defruled lemma2
       (implies (natp j)
                (integerp (* 1/2 (- (expt 5 j) 1))))
      :induct (acl2::dec-induct j)
      :hints (("subgoal *1/2" :use
               (:instance lemma1
                          (k (* 1/2 (- (expt 5 (1- j)) 1))))))))
    (acl2::with-arith5-nonlinear-help
     (defruled lemma3
       (not (evenp (expt 5 k)))
       :cases ((>= k 0) (< k 0))
       :hints (("subgoal 2" :use (:instance lemma2 (j k)))
               ("subgoal 1" :cases ((< (expt 5 k) 1))))))
    (acl2::with-arith5-help
    (defruled lemma4
      (implies (posp i)
               (not (equal (expt 2 i) (expt 5 j))))
      :use (:instance lemma3 (k j))))
    (acl2::with-arith5-help
     (defruled lemma5
       (implies (not (zip i))
                (not (equal (expt 2 i) (expt 5 j))))
       :use (lemma4
             (:instance lemma4 (i (- i)) (j (- j))))))
    (defruled lemma6
     (implies (posp k)
              (< (expt 2 k) (expt (D) k)))
     :induct (acl2::dec-induct k)
     :enable D))))

(defruled Gp-as-ordD
  (implies (and (integerp p) (<= 2 p))
           (equal (Gp p)
                  (- (ordD (expt 2 (- p 1))) 1)))
  :enable (Gp 2^p-is-not-D^k)
  :use (:instance result-1-3
                  (x (expt 2 (- p 1)))
                  (k (+ (Gp p) 1))))

(acl2::with-arith5-help
 (define starting-length
  ((c natp))
  :returns (from-i (and (integerp from-i) (< 1 from-i))
                   :rule-classes :type-prescription)
  (let* ((c (nfix c))
         (p (if (= c 0) 0 (ord2 c))))
    (max (- (ordD (expt 2 (- p 1))) 1) 2))
  ///
  (fty::deffixequiv starting-length)
  (defruled starting-length-alt
    (equal (starting-length c)
           (let* ((c (nfix c))
                  (p (if (zp c) 0 (ord2 c))))
             (max (Gp p) 2)))
    :cases ((zp c) (>= (ord2 c) 2))
    :hints (("subgoal 3" :in-theory (enable ord2)
             :cases ((= c 1) (= c 2) (= c 3))
             :use (:instance expe-monotone
                             (b 2)
                             (x 4)
                             (y c)))
            ("subgoal 1" :use (:instance Gp-as-ordD
                                         (p (ord2 c))))))
  (defruled starting-length-monotone
    (implies (<= (nfix c1) (nfix c2))
             (<= (starting-length c1) (starting-length c2)))
    :enable ord2
    :use ((:instance result-1-4
                     (x (expt 2 (1- (ord2 c1))))
                     (y (expt 2 (1- (ord2 c2)))))
          (:instance expe-monotone
                     (b 2)
                     (x c1)
                     (y c2))))))

(defrule starting-length-when-c<128
  (implies (< (nfix c) 128)
           (equal (starting-length c) 2))
  :use (:instance starting-length-monotone
                  (c1 c)
                  (c2 127)))

(defrule starting-length-when-normal
  (implies (and (finite-positive-binary-p v f)
                (>= v (MIN_NORMAL f)))
           (equal (starting-length (c v f)) (max (G f) 2)))
  :enable (starting-length-alt G 2^{P-1} ord2)
  :use ((:instance expe-unique
                   (b 2)
                   (x (c v f))
                   (n (1- (P f))))
        (:instance c-vs-MIN_NORMAL (x v))))

; It is not necessary do decrease c for correctness of Result-6
(defrule result-6
  (implies (finite-positive-binary-p v f)
           (equal (algo1 (starting-length (c v f)) v f)
                  (algo1 2 v f)))
  :enable (starting-length-alt ord2 expe-lower-bound)
  :use (:instance better-start-when-c>=2^{p-1}
                  (from-i 2)
                  (p (ord2 (c v f)))))

; Result-6 as it is in the paper
(defrule result-6-in-the-paper
  (implies (finite-positive-binary-p v f)
           (equal (algo1 (starting-length (- (c v f) 1)) v f)
                  (algo1 2 v f)))
  :enable (starting-length-alt ord2 expe-lower-bound)
  :use (:instance better-start-when-c>=2^{p-1}
                  (from-i 2)
                  (p (if (= (c v f) 1) 0 (ord2 (1- (c v f)))))))
