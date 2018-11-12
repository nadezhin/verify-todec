(in-package "RTL")
(include-book "section6")

(local (include-book "rtl/rel11/support/basic" :dir :system))
(local (acl2::allow-arith5-help))

(defruled wid-Rv-as-vr-vl
  (equal (wid-Rv v f)
         (- (vr v f) (vl v f)))
  :enable (wid-Rv-as-c-q vl-alt vr))

(acl2::with-arith5-nonlinear-help
 (defruled result-4
  (implies (and (in-tau-intervalp (D-value d1 i) (Rv v f))
                (< (wid-Rv v f) (expt (D) i))
                (not (= (ifix d1) (ifix d2))))
           (not (in-tau-intervalp (D-value d2 i) (Rv v f))))
  :enable (in-tau-intervalp-Rv wid-Rv-as-vr-vl D-value)
  :cases ((<= (ifix d1) (1- (ifix d2)))
          (>= (ifix d1) (1+ (ifix d2))))))

(defrulel result-5-subcase<
 (implies (> (wid-Rv v f) (expt (D) i))
          (or (in-tau-intervalp (u_i v i) (Rv v f))
              (in-tau-intervalp (w_i v i) (Rv v f))))
 :rule-classes ()
 :enable (in-tau-intervalp-Rv wid-Rv-as-vr-vl u_i-linear w_i-linear)
 :cases ((< (vl v f) (u_i v i))
         (< (w_i v i) (vr v f)))
 :hints (("subgoal 3" :in-theory (enable u_i w_i t_i))))

(local
 (acl2::with-arith5-help
  (defrule result-5-subcase=-lemma
    (implies (and (integerp i)
                  (= (wid-Rv v f) (expt (D) i)))
             (equal i 0))
    :rule-classes ()
    :enable (wid-Rv-as-c-q expt-D-as-expt-D/2)
    :disable mod
    :cases ((or (not (= (c v f) (2^{P-1} f))) (= (q v f) (Qmin f))))
    :hints
    (("subgoal 2" :cases ((< (+ -2 (- i) (q v f)) 0)
                          (= (+ -2 (- i) (q v f)) 0)
                          (> (+ -2 (- i) (q v f)) 0)))
     ("subgoal 2.3" :use (:instance mod-expt-3*D/2 (i (- i))))
     ("subgoal 2.1" :use ((:instance even-odd
                                     (x (* 3 (expt 2 (+ -2 (- i) (q v f)))))
                                     (y (expt (D/2) i)))
                          mod-expt-D/2
                          (:instance mod-expt-c*2^q
                                     (c 3)
                                     (q (+ -2 (- i) (q v f)))
                                     )))
     ("subgoal 1" :cases ((< (+ (- i) (q v f)) 0)
                          (= (+ (- i) (q v f)) 0)
                          (> (+ (- i) (q v f)) 0)))
     ("subgoal 1.3" :use (:instance mod-expt-D/2 (i (- i))))
     ("subgoal 1.1" :use mod-expt-D/2))
    :prep-lemmas
    ((defrule mod-lemma
       (implies (and (integerp x)
                     (integerp y))
                (equal (mod (* x y) 2)
                       (mod (* (mod x 2) (mod y 2)) 2)))
       :rule-classes ()
       :use (:instance lemma
                       (x (1+ x))
                       (y (1+ y)))
       :prep-lemmas
       ((defruled lemma
          (implies (and (= (mod x 2) 0)
                        (= (mod y 2) 0))
                   (equal (mod (* x y) 2) 0)))))
     (defruled mod-expt-D/2-i>=0
       (implies (natp i)
                (equal (mod (expt (D/2) i) 2) 1))
       :induct (sub1-induction i)
       :hints (("subgoal *1/2" :in-theory (enable D/2)
                :use (:instance mod-lemma
                                (x (expt (D/2) (1- i)))
                                (y (D/2))))))
     (defruled mod-expt-D/2
       (implies (integerp i)
                (not (equal (mod (expt (D/2) i) 2) 0)))
       :use mod-expt-D/2-i>=0)
     (defruled mod-expt-3*D/2
       (implies (integerp i)
                (not (equal (mod (* 3 (expt (D/2) i)) 2) 0)))
       :use (mod-expt-D/2-i>=0
             (:instance mod-lemma
                        (x 3)
                        (y (expt (D/2) i))))
       :enable D/2)
     (defruled mod-expt-c*2^q
       (implies (and (integerp c)
                     (posp q))
                (equal (mod (* c (expt 2 q)) 2) 0)))
     (defruled even-odd
       (implies (and (= (mod x 2) 0)
                     (not (= (mod y 2) 0)))
                (not (= x y))))
     (defrule expt-D/2!=3
       (not (equal (expt (D/2) i) 3))
       :enable D/2
       :cases ((<= (ifix i) 0) (>= (ifix i) 1)))))))

(local
 (acl2::with-arith5-help
  (defrule result-5-subcase=
    (implies (and (= (wid-Rv v f) (expt (D) i))
                  (finite-positive-binary-p v f)
                  (integerp i)
                  (pos-rationalp v))
             (in-tau-intervalp (u_i v i) (Rv v f)))
    :rule-classes ()
    :enable (in-tau-intervalp-Rv
             wid-Rv-as-c-q u_i s_i vl vr c)
    :use (result-5-subcase=-lemma
          (:instance c-type-when-finite-positive-binary
                     (x v)))
    :prep-lemmas
    ((defrule lemma0
       (implies (integerp q)
                (not (equal (expt 2 q) 4/3)))
       :cases ((<= q 0) (>= q 1)))
     (acl2::with-arith5-nonlinear-help
      (defrule lemma
        (implies (and (finite-positive-binary-p v f)
                      (= (wid-Rv v f) 1))
                 (integerp v))
        :enable wid-Rv-as-c-q
        :use (:instance finite-positive-binary-necc
                        (x v))))))))

(defrule result-5
  (implies (and (>= (wid-Rv v f) (expt (D) (ifix i)))
                (finite-positive-binary-p v f))
           (or (in-tau-intervalp (u_i v i) (Rv v f))
               (in-tau-intervalp (w_i v i) (Rv v f))))
  :rule-classes ()
  :do-not-induct t
  :use (result-5-subcase<
        (:instance result-5-subcase=
                   (i (ifix i)))))

