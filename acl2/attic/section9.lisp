(in-package "RTL")
(include-book "section8")

(local (acl2::allow-arith5-help))

(defrule better-start-when-c>=2^{p-1}
  (implies (and (posp from-i)
                (>= (c v f) (expt 2 (- (ifix p) 1)))
                (< from-i (Gp p)))
           (equal (algo1 from-i v f)
                  (algo1 (Gp p) v f)))
  :cases ((< (algo1-i from-i v f) (Gp p)))
  :hints
  (("subgoal 2" :in-theory (enable algo1))
   ("subgoal 1" :in-theory (disable has-D-length-algo1) :use
    ((:instance result-4-part-1-when-c>=2^{p-1}
                (i (Gp p))
                (v (pos-rational-fix v))
                (d1 (algo1 from-i v f))
                (d2 (algo1 (Gp p) v f))
                )
     (:instance has-D-length-monotone
                (x (algo1 from-i v f))
                (i (algo1-i from-i v f))
                (j (Gp p)))
     (:instance algo1-i<=max-from-i-j
                (d (algo1 from-i v f))
                (from-i (Gp p))
                (j (algo1-i from-i v f)))
     has-D-length-algo1
     (:instance has-D-length-algo1
                (from-i (Gp p))))))
  :prep-lemmas
  ((defrule lemma
     (implies (and (posp from-i)
                   (posp from-j)
                   (< from-i from-j))
              (implies (>= (algo1-i from-i v f) from-j)
                       (equal (algo1-i from-i v f)
                              (algo1-i from-j v f))))
     :enable algo1-i
     :induct (algo1-i from-i v f))))

(acl2::with-arith5-nonlinear++-help
 (defrule result-5
   (implies (and (posp from-i)
                 (< from-i (G f))
                 (<= (MIN_NORMAL f) (pos-rational-fix v)))
            (equal (algo1 from-i v f)
                   (algo1 (G f) v f)))
   :enable (c 2^{P-1} G)
   :use ((:instance better-start-when-c>=2^{p-1}
                    (p (P f)))
         (:instance MIN_NORMAL-lemma
                    (v (pos-rational-fix v))))))
