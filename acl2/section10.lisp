(in-package "RTL")
(include-book "section9")

(local (include-book "rtl/rel11/support/float" :dir :system))
(local (acl2::allow-arith5-help))

(defruled Gp-as-ordD
  (implies (and (integerp p) (<= 2 p))
           (equal (Gp p)
                  (- (ordD (expt 2 (- p 1))) 1)))
  :enable (Gp powers-of-2-and-D-are-distinct)
  :use ((:instance powers-of-2-and-D-are-distinct
                   (i (1- p))
                   (j (1- (ordD (expt 2 (1- p))))))
        (:instance result-1-3
                   (x (expt 2 (- p 1)))
                   (k (+ (Gp p) 1)))))

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
