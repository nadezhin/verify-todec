#|
(include-book "rtl/rel11/portcullis" :dir :system)
|#
(in-package "RTL")
(include-book "section9")

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
                  (- (OrdD (expt 2 (- p 1))) 1)))
  :enable (Gp 2^p-is-not-D^k)
  :use (:instance result-1-3
                  (x (expt 2 (- p 1)))
                  (k (+ (Gp p) 1))))
