#|
(include-book "rtl/rel11/portcullis" :dir :system)
|#
(in-package "RTL")
(include-book "section3")

(local (include-book "rtl/rel11/support/basic" :dir :system))
(local (acl2::allow-arith5-help))

(define frac
   ((x real/rationalp))
   :returns (frac (and (real/rationalp frac)
                       (<= 0 frac)
                       (< frac 1))
                  :rule-classes :type-prescription)
   (re (realfix x))
   ///
   (fty::deffixequiv frac)
   (defrule frac-linear
     (< (frac x) 1)
     :rule-classes :linear)
   (defrule frac-int
     (implies (integerp x)
              (equal (frac x) 0)))
   (acl2::with-arith5-help
    (defruled frac-+
      (implies (and (real/rationalp x)
                    (real/rationalp y))
               (equal (frac (+ x y))
                      (if (< (+ (frac x) (frac y)) 1)
                          (+ (frac x) (frac y))
                        (+ -1 (frac x) (frac y)))))
      :enable fl)))

(define frac-alpha-d
  ((alpha pos-rationalp)
   (d natp))
  :returns (frac (and (real/rationalp frac)
                      (<= 0 frac)
                      (< frac 1))
                 :rule-classes :type-prescription)
  (frac (* (pos-rational-fix alpha) (nfix d)))
  ///
  (fty::deffixequiv frac-alpha-d)
  (defrule frac-alpha-d-linear
    (< (frac-alpha-d alpha d) 1)
    :rule-classes :linear)
  (defrule frac-alpha-d-+
    (let ((fr+ (+ (frac-alpha-d alpha d1)
                  (frac-alpha-d alpha d2))))
      (implies (and (natp d1)
                    (natp d2))
               (equal (frac-alpha-d alpha (+ d1 d2))
                      (if (< fr+ 1) fr+ (- fr+ 1)))))
    :enable frac-+))
   
(acl2::with-arith5-nonlinear-help
 (defrule frac-alpha-d-arith-progression-up
  (implies
   (and (natp i)
        (posp prev-den)
        (posp cur-den)
        (< (* (frac-alpha-d alpha cur-den) i)
           (- 1 (frac-alpha-d alpha prev-den))))
   (equal (frac-alpha-d alpha (+ prev-den (* cur-den i)))
          (+ (frac-alpha-d alpha prev-den)
             (* (frac-alpha-d alpha cur-den) i))))
  :induct (sub1-induction i)
  :hints (("subgoal *1/2" :use (:instance frac-alpha-d-+
                                          (d1 (+ prev-den (* cur-den (1- i))))
                                          (d2 cur-den))))))

(acl2::with-arith5-nonlinear-help
 (defrule frac-alpha-d-arith-progression-up=
  (implies
   (and (natp i)
        (posp prev-den)
        (posp cur-den)
        (= (* (frac-alpha-d alpha cur-den) i)
           (- 1 (frac-alpha-d alpha prev-den))))
   (equal (frac-alpha-d alpha (+ prev-den (* cur-den i)))
          0))
  :cases ((posp i))
  :use ((:instance frac-alpha-d-arith-progression-up
                   (i (1- i)))
        (:instance frac-alpha-d-+
                   (d1 (+ prev-den (* cur-den (1- i))))
                   (d2 cur-den)))))

(acl2::with-arith5-nonlinear-help
 (defrule frac-alpha-d-arith-progression-down
  (implies
   (and (natp i)
        (posp prev-den)
        (posp cur-den)
        (<= (* (- 1 (frac-alpha-d alpha cur-den)) i)
            (frac-alpha-d alpha prev-den)))
   (equal (frac-alpha-d alpha (+ prev-den (* cur-den i)))
          (- (frac-alpha-d alpha prev-den)
             (* (- 1 (frac-alpha-d alpha cur-den)) i))))
  :induct (sub1-induction i)
  :hints (("subgoal *1/2" :use (:instance frac-alpha-d-+
                                          (d1 (+ prev-den (* cur-den (1- i))))
                                          (d2 cur-den))))))
 
(define frac-alpha-d-in
  :long "for all i in [1,n) frac(alpha*i) in [lo,hi]"
  ((alpha pos-rationalp)
   (n posp)
   (lo rationalp)
   (hi rationalp))
  :returns (yes booleanp)
  (or (not (integerp n))
      (<= n 1)
      (let ((frac (frac-alpha-d alpha (1- n))))
        (and (<= (rfix lo) frac)
             (<= frac (rfix hi))
             (frac-alpha-d-in alpha (1- n) lo hi))))
  ///
  (fty::deffixequiv frac-alpha-d-in
                    :hints (("goal" :in-theory (enable acl2::pos-fix))))
  (defruled frac-alpha-d-in-monotonic-by-n
    (implies (and (frac-alpha-d-in alpha n2 lo hi)
                  (<= (acl2::pos-fix n) (acl2::pos-fix n2)))
             (frac-alpha-d-in alpha n lo hi))
    :enable acl2::pos-fix)
  (defruled frac-alpha-d-in-monotonic-by-lo
    (implies (and (frac-alpha-d-in alpha n lo2 hi)
                  (<= (rfix lo) (rfix lo2)))
             (frac-alpha-d-in alpha n lo hi)))
  (defruled frac-alpha-d-in-monotonic-by-hi
    (implies (and (frac-alpha-d-in alpha n lo hi2)
                  (<= (rfix hi2) (rfix hi)))
             (frac-alpha-d-in alpha n lo hi)))
  (acl2::with-arith5-help
   (defruled frac-alpha-d-in-necc
     (implies (and (frac-alpha-d-in alpha n lo hi)
                   (posp i)
                   (< i (acl2::pos-fix n)))
              (let ((frac (frac-alpha-d alpha i)))
                (and (<= (rfix lo) frac)
                     (<= frac (rfix hi)))))
     :enable acl2::pos-fix))
  (defruled frac-alpha-d-in-lemma
    (implies
     (and (frac-alpha-d-in alpha n1 lo1 hi1)
          (frac-alpha-d-in alpha n2 lo2 hi2)
          (<= 0 lo)
          (< hi 1)
          (<= lo lo1)
          (<= hi1 hi)
          (<= lo (frac-alpha-d alpha n1))
          (<= (frac-alpha-d alpha n1) hi)
          (<= n (+ n1 n2))
          (rationalp lo)
          (rationalp hi)
          (rationalp lo1)
          (rationalp hi1)
          (rationalp lo2)
          (rationalp hi2)
          (posp n1)
          (posp n2)
          (or (<= (+ 1 lo) (+ (frac-alpha-d alpha n1) lo2))
              (<= (+ (frac-alpha-d alpha n1) hi2) hi)))
     (frac-alpha-d-in alpha n lo hi))
    :induct (sub1-induction n)
    :enable frac-alpha-d-in
    :hints
    (("subgoal *1/2" :cases ((<= (acl2::pos-fix n) n1)
                             (= (acl2::pos-fix n) (1+ n1))
                             (> (acl2::pos-fix n) (1+ n1))))
     ("subgoal *1/2.3" :use (:instance frac-alpha-d-in-necc
                                       (i (1- (acl2::pos-fix n)))
                                       (n n1)
                                       (lo lo1)
                                       (hi hi1)))
     ("subgoal *1/2.2" :use (:instance frac-alpha-d-in-monotonic-by-lo
                                       (n n1)
                                       (lo2 lo1)))
     ("subgoal *1/2.1" :cases ((< (+ (frac-alpha-d alpha n1)
                                     (frac-alpha-d alpha (+ -1 n (- n1))))
                                  1))
      :use ((:instance frac-alpha-d-+
                       (d1 n1)
                       (d2 (+ -1 n (- n1))))
            (:instance frac-alpha-d-in-necc
                       (i (+ -1 n (- n1)))
                       (n n2)
                       (lo lo2)
                       (hi hi2)))))))


(acl2::with-arith5-help
 (defruled frac-alpha-d-even
  (acl2::b*
   ((prev-frac (frac-alpha-d alpha prev-den))
    (cur-frac (frac-alpha-d alpha cur-den)))
   (implies
    (and (natp i)
         (frac-alpha-d-in alpha cur-den (+ cur-frac (- 1 prev-frac)) prev-frac)
         (posp prev-den)
         (posp cur-den)
         (<= prev-den cur-den)
         (<= cur-frac prev-frac)
         (< (* i cur-frac) (- 1 prev-frac)))
    (frac-alpha-d-in
     alpha
     (+ prev-den (* (1+ i) cur-den))
     cur-frac
     (+ prev-frac (* i cur-frac)))))
  :induct (sub1-induction i)
  :enable frac-alpha-d-in-monotonic-by-n
  :hints
  (("subgoal *1/2" :use (:instance frac-alpha-d-in-lemma
                                   (n1 (+ prev-den (* i cur-den)))
                                   (lo1 (frac-alpha-d alpha cur-den))
                                   (hi1 (+ (frac-alpha-d alpha prev-den)
                                           (* (1- i) (frac-alpha-d alpha cur-den))))
                                   (n2 cur-den)
                                   (lo2 (+ (frac-alpha-d alpha cur-den)
                                           (- 1 (frac-alpha-d alpha prev-den))))
                                   (hi2 (frac-alpha-d alpha prev-den))
                                   (n (+ prev-den (* (1+ i) cur-den)))
                                   (lo (frac-alpha-d alpha cur-den))
                                   (hi (+ (frac-alpha-d alpha prev-den)
                                          (* i (frac-alpha-d alpha cur-den))))))
   ("subgoal *1/1" :use (:instance frac-alpha-d-in-lemma
                                   (n1 prev-den)
                                   (lo1 (+ (frac-alpha-d alpha cur-den)
                                           (- 1 (frac-alpha-d alpha prev-den))))
                                   (hi1 (frac-alpha-d alpha prev-den))
                                   (n2 cur-den)
                                   (lo2 (+ (frac-alpha-d alpha cur-den)
                                           (- 1 (frac-alpha-d alpha prev-den))))
                                   (hi2 (frac-alpha-d alpha prev-den))
                                   (n (+ prev-den cur-den))
                                   (lo (frac-alpha-d alpha cur-den))
                                   (hi (frac-alpha-d alpha prev-den)))))))

(acl2::with-arith5-nonlinear-help
 (defruled frac-alpha-d-even-corr
  (acl2::b*
   ((prev-frac (frac-alpha-d alpha prev-den))
    (cur-frac (frac-alpha-d alpha cur-den))
    (q (fl (/ (- 1 prev-frac) cur-frac))))
   (implies
    (and (posp q)
         (frac-alpha-d-in alpha cur-den (+ cur-frac (- 1 prev-frac)) prev-frac)
         (posp prev-den)
         (posp cur-den)
         (<= prev-den cur-den)
         (<= cur-frac prev-frac))
    (frac-alpha-d-in
     alpha
     (+ prev-den (* q cur-den))
     cur-frac
     (+ prev-frac (* (1- q) cur-frac)))))
  :use ((:instance frac-alpha-d-even
                   (i (1- (fl (/ (- 1 (frac-alpha-d alpha prev-den))
                                 (frac-alpha-d alpha cur-den))))))
        (:instance fl-def
                   (x (/ (- 1 (frac-alpha-d alpha prev-den))
                         (frac-alpha-d alpha cur-den)))))))
 

(acl2::with-arith5-nonlinear-help
 (defruled frac-alpha-d-odd
  (acl2::b*
   ((prev-frac (frac-alpha-d alpha prev-den))
    (cur-frac (frac-alpha-d alpha cur-den)))
   (implies
    (and (natp i)
         (frac-alpha-d-in alpha cur-den prev-frac (- cur-frac prev-frac))
         (posp prev-den)
         (posp cur-den)
         (<= prev-den cur-den)
         (<= prev-frac cur-frac)
         (< (* i (- 1 cur-frac)) prev-frac))
    (frac-alpha-d-in
     alpha
     (+ prev-den (* (1+ i) cur-den))
     (- prev-frac (* i (- 1 cur-frac)))
     cur-frac)))
  :induct (sub1-induction i)
  :enable frac-alpha-d-in-monotonic-by-n
  :hints
  (("subgoal *1/2" :use (:instance frac-alpha-d-in-lemma
                                   (n1 (+ prev-den (* i cur-den)))
                                   (lo1 (- (frac-alpha-d alpha prev-den)
                                           (* (1- i) (- 1 (frac-alpha-d alpha cur-den)))))
                                   (hi1 (frac-alpha-d alpha cur-den))
                                   (n2 cur-den)
                                   (lo2 (frac-alpha-d alpha prev-den))
                                   (hi2 (- (frac-alpha-d alpha cur-den)
                                           (frac-alpha-d alpha prev-den)))
                                   (n (+ prev-den (* (1+ i) cur-den)))
                                   (lo (- (frac-alpha-d alpha prev-den)
                                          (* i (- 1 (frac-alpha-d alpha cur-den)))))
                                   (hi (frac-alpha-d alpha cur-den))))
   ("subgoal *1/1"
    :use (:instance frac-alpha-d-in-lemma
                                   (n1 prev-den)
                                   (lo1 (frac-alpha-d alpha prev-den))
                                   (hi1 (- (frac-alpha-d alpha cur-den)
                                           (frac-alpha-d alpha prev-den)))
                                   (n2 cur-den)
                                   (lo2 (frac-alpha-d alpha prev-den))
                                   (hi2 (- (frac-alpha-d alpha cur-den)
                                           (frac-alpha-d alpha prev-den)))
                                   (n (+ prev-den cur-den))
                                   (lo (frac-alpha-d alpha prev-den))
                                   (hi (frac-alpha-d alpha cur-den)))))))

(acl2::with-arith5-nonlinear++-help
 (defruled frac-alpha-d-odd-corr
  (acl2::b*
   ((prev-frac (frac-alpha-d alpha prev-den))
    (cur-frac (frac-alpha-d alpha cur-den))
    (q (fl (/ prev-frac (- 1 cur-frac)))))
   (implies
    (and (posp q)
         (frac-alpha-d-in alpha cur-den prev-frac (- cur-frac prev-frac))
         (posp prev-den)
         (posp cur-den)
         (<= prev-den cur-den)
         (<= prev-frac cur-frac))
    (frac-alpha-d-in
     alpha
     (+ prev-den (* q cur-den))
     (- prev-frac (* (1- q) (- 1 cur-frac)))
     cur-frac)))
  :use ((:instance frac-alpha-d-odd
                   (i (1- (fl (/ (frac-alpha-d alpha prev-den)
                                 (- 1 (frac-alpha-d alpha cur-den)))))))
        (:instance fl-def
                   (x (/ (frac-alpha-d alpha prev-den)
                         (- 1 (frac-alpha-d alpha cur-den))))))))

(acl2::with-arith5-nonlinear-help
 (define frac-alpha-d-bound-aux
  ((alpha pos-rationalp)
   (cur-den posp)
   (prev-den posp)
   (odd booleanp)
   (max-den posp))
  :returns (mv (den posp :rule-classes :type-prescription)
               (lo rationalp :rule-classes :type-prescription)
               (hi rationalp :rule-classes :type-prescription))
  :measure (nfix (- (1+ (acl2::pos-fix max-den))
                    (acl2::pos-fix cur-den)))
  (acl2::b*
   (;(alpha (pos-rational-fix alpha))
    (cur-den (acl2::pos-fix cur-den))
    (prev-den (acl2::pos-fix prev-den))
    (max-den (acl2::pos-fix max-den))
    (cur-frac (frac-alpha-d alpha cur-den))
    (prev-frac (frac-alpha-d alpha prev-den))
    (lo (if odd
            prev-frac
          (+ cur-frac (- 1 prev-frac))))
    (hi (if odd
            (- (if (= cur-frac 0) 1 cur-frac) prev-frac)
          prev-frac))
    ((when (= cur-frac 0)) (mv cur-den lo hi))
    (q-pre (if odd
               (/ prev-frac (- 1 cur-frac))
             (/ (- 1 prev-frac) cur-frac)))
    (q (fl q-pre))
    ((when (or (< q 1)
               (< cur-den prev-den)
               (< max-den cur-den)
               (if odd
                   (< cur-frac prev-frac)
                 (< prev-frac cur-frac))))
     (mv cur-den lo hi)))
   (frac-alpha-d-bound-aux alpha (+ prev-den (* q cur-den)) cur-den (not odd) max-den))
  ///
  (fty::deffixequiv frac-alpha-d-bound-aux)))


#|
(acl2::with-arith5-help
 (rule
 (acl2::b*
  (;(alpha (pos-rational-fix alpha))
    ;(cur-den (acl2::pos-fix cur-den))
    ;(prev-den (acl2::pos-fix prev-den))
    (max-den (acl2::pos-fix max-den))
    (cur-frac (frac-alpha-d alpha cur-den))
    (prev-frac (frac-alpha-d alpha prev-den))
    (cur-lo (if odd
                prev-frac
              (+ cur-frac (- 1 prev-frac))))
    (cur-hi (if odd
                (- (if (= cur-frac 0) 1 cur-frac) prev-frac)
              prev-frac))
    ((mv den lo hi) (frac-alpha-d-bound-aux alpha cur-den prev-den odd max-den))
   )
 (implies
  (and (frac-alpha-d-in alpha cur-den cur-lo cur-hi)
       (pos-rationalp alpha)
       (posp prev-den)
       (posp cur-den)
       (posp max-den)
       (<= prev-den cur-den)
       (if odd
           (<= (frac-alpha-d alpha prev-den) (frac-alpha-d alpha cur-den))
         (<= (frac-alpha-d alpha cur-den) (frac-alpha-d alpha prev-den)))
       )
  (frac-alpha-d-in alpha den lo hi)))
 :induct (frac-alpha-d-bound-aux alpha cur-den prev-den odd max-den)
 :enable (frac-alpha-d-bound-aux)
 :disable frac-alpha-d-+
 :hints (("subgoal *1/3" :cases (odd) :do-not-induct t)
         ("subgoal *1/3.2" :by lemma-1/3.2)
         ("subgoal *1/3.1" :by lemma-1/3.1)
;         ("subgoal *1/3.2.3" :by lemma-1/3.2.3)
;         ("subgoal *1/3.2.2" :by lemma-1/3.2.2)
;         ("subgoal *1/3.2.1" :by lemma-1/3.2.1)
;         ("subgoal *1/3.1.5" :by lemma-1/3.1.5)
;         ("subgoal *1/3.1.3" :by lemma-1/3.1.3)
;         ("subgoal *1/3.1.1" :by lemma-1/3.1.1)
         )
 ))))
 :prep-lemmas
 ((acl2::with-arith5-nonlinear-help
   (defrule lemma
    (implies
     (and (<= (frac-alpha-d alpha cur-den) (frac-alpha-d alpha prev-den))
          (posp cur-den)
          (posp prev-den)
          (posp (fl (/ (- 1 (frac-alpha-d alpha prev-den))
                       (frac-alpha-d alpha cur-den))))
          )
     (<= (frac-alpha-d alpha cur-den)
         (frac-alpha-d alpha (+ prev-den
                                (* cur-den (fl (/ (- 1 (frac-alpha-d alpha prev-den))
                                                  (frac-alpha-d alpha
                                                                cur-den))))))))
    :use ((:instance frac-alpha-d-arith-progression-up
                     (i (fl (/ (- 1 (frac-alpha-d alpha prev-den))
                               (frac-alpha-d alpha cur-den)))))
;          (:instance fl-def (x (/ (- 1 (frac-alpha-d alpha prev-den))
;                                  (frac-alpha-d alpha cur-den)))))
    ))
 ))
 ))
|#

(acl2::with-arith5-nonlinear-help
 (define frac-alpha-d-bound
  ((alpha pos-rationalp)
   (max-den posp))
  :returns (mv (den posp :rule-classes :type-prescription)
               (lo rationalp :rule-classes :type-prescription)
               (hi rationalp :rule-classes :type-prescription))
  (acl2::b*
   ((alpha (pos-rational-fix alpha))
    (max-den (acl2::pos-fix max-den))
    (frac (frac alpha)))
   (cond ((= frac 0) (mv 1 1 0))
         ((< frac 1/2)
          (frac-alpha-d-bound-aux alpha (fl (/ frac)) 1 t max-den))
         ((> frac 1/2)
          (frac-alpha-d-bound-aux alpha (fl (/ (- 1 frac))) 1 nil max-den))
         (t (mv 2 1/2 1/2))))
  :guard-hints
  (("goal" :use
    (:instance n<=fl-linear
               (n 2)
               (x (/ (- 1 (frac (pos-rational-fix alpha))))))))
  ///
  (fty::deffixequiv frac-alpha-d-bound)))

(define frac-alpha-d-bound-q
  ((q integerp)
   (max-den posp))
  :returns (mv (den posp :rule-classes :type-prescription)
               (lo rationalp :rule-classes :type-prescription)
               (hi rationalp :rule-classes :type-prescription))
  (acl2::b*
   ((q (ifix q))
    (max-den (acl2::pos-fix max-den))
    (ulp2 (expt 2 q))
    (r (1- (ordD ulp2)))
    (ulpD (expt (D) r))
    (alpha (/ ulp2 ulpD)))
   (frac-alpha-d-bound alpha max-den))
  ///
  (fty::deffixequiv frac-alpha-d-bound-q))

(acl2::with-arith5-help
 (define frac-alpha-d-bound-f
   ((f formatp)
    (q integerp)
    (acc true-listp))
   :measure (nfix (- (1+ (ifix q)) (Qmin f)))
   (acl2::b*
    ((q (ifix q))
     ((unless (<= (Qmin f) q)) acc)
     ((mv den lo hi) (frac-alpha-d-bound-q q (+ (expt 2 (1+ (P f))) 2))))
    (frac-alpha-d-bound-f
     f
     (1- q)
     (cons (list q den lo hi) acc)))))

(defconst *dp-bounds* (frac-alpha-d-bound-f (dp) (- 1023 52) nil))

(define collect
  ((bounds true-listp))
  (and bounds
       (if (atom (cdr bounds))
           (list (nth 1 (acl2::list-fix (car bounds)))
                 (nth 2 (acl2::list-fix (car bounds)))
                 (nth 3 (acl2::list-fix (car bounds))))
         (acl2::b*
          ((hd (acl2::list-fix (car bounds)))
           (tail (collect (cdr bounds))))
          (list (max (rfix (nth 1 hd)) (rfix (nth 0 tail)))
                (min (rfix (nth 2 hd)) (rfix (nth 1 tail)))
                (max (rfix (nth 3 hd)) (rfix (nth 2 tail))))))))

(rule
 (and (equal (expo (nth 1 (collect *dp-bounds*))) -64)
      (equal (expo (- 1 (nth 2 (collect *dp-bounds*)))) -64)))


#|
Output from net.java.jinterval.text2interval.fractions.Fractions:

alpha = 43/33
 = 1 + 1/(3 + 1/(3 + 1/(3)))
 1/1 4/3 13/10 43/33
frac(alpha*1) = 10/33
0 < i < 2 ==> 10/33 <= frac(alpha*i) <= 10/33
frac(alpha*2) = 20/33
0 < i < 3 ==> 10/33 <= frac(alpha*i) <= 20/33
frac(alpha*3) = 10/11
0 < i < 4 ==> 10/33 <= frac(alpha*i) <= 10/11
frac(alpha*4) = 7/33
0 < i < 7 ==> 7/33 <= frac(alpha*i) <= 10/11
frac(alpha*7) = 4/33
0 < i < 10 ==> 4/33 <= frac(alpha*i) <= 10/11
frac(alpha*10) = 1/33
0 < i < 13 ==> 1/33 <= frac(alpha*i) <= 10/11
frac(alpha*13) = 31/33
0 < i < 23 ==> 1/33 <= frac(alpha*i) <= 31/33
frac(alpha*23) = 32/33
0 < i < 33 ==> 1/33 <= frac(alpha*i) <= 32/33
frac(alpha*33) = 0
|#
(defconst *alpha* 43/33)

(rule
 (and
  (equal (frac-alpha-d-bound *alpha* 1) (list 3 10/33 20/33))
  (equal (frac-alpha-d-bound *alpha* 3) (list 10 4/33 10/11))
  (equal (frac-alpha-d-bound *alpha* 10) (list 33 1/33 32/33))))

(defrule frac-alpha-d-i<1
  (frac-alpha-d-in *alpha* 1 1 0))

(defrule frac-alpha-d-i<2
  (frac-alpha-d-in *alpha* 2 10/33 10/33)
  :use (:instance frac-alpha-d-in-lemma
                  (alpha *alpha*)
                  (n1 1) (lo1 1) (hi1 0)
                  (n2 1) (lo2 1) (hi2 0)
                  (n 2) (lo 10/33) (hi 10/33))
  :disable ((frac-alpha-d-in)))

(defrule frac-alpha-d-i<3
  (frac-alpha-d-in *alpha* 3 10/33 20/33)
  :use (:instance frac-alpha-d-in-lemma
                  (alpha *alpha*)
                  (n1 2) (lo1 10/33) (hi1 10/33)
                  (n2 1) (lo2 1) (hi2 0)
                  (n 3) (lo 10/33) (hi 20/33))
  :disable ((frac-alpha-d-in)))

(defrule frac-alpha-d-i<4
  (frac-alpha-d-in *alpha* 4 10/33 10/11)
  :use (:instance frac-alpha-d-in-lemma
                  (alpha *alpha*)
                  (n1 1) (lo1 1) (hi1 0)
                  (n2 3) (lo2 10/33) (hi2 20/33)
                  (n 4) (lo 10/33) (hi 10/11))
  :disable ((frac-alpha-d-in)))

(defrule frac-alpha-d-i<7
  (frac-alpha-d-in *alpha* 7 7/33 10/11)
  :use (:instance frac-alpha-d-in-lemma
                  (alpha *alpha*)
                  (n1 4) (lo1 10/33) (hi1 10/11)
                  (n2 3) (lo2 10/33) (hi2 20/33)
                  (n 7) (lo 7/33) (hi 10/11))
  :disable ((frac-alpha-d-in)))

(defrule frac-alpha-d-i<10
  (frac-alpha-d-in *alpha* 10 4/33 10/11)
  :use (:instance frac-alpha-d-in-lemma
                  (alpha *alpha*)
                  (n1 7) (lo1 7/33) (hi1 10/11)
                  (n2 3) (lo2 10/33) (hi2 20/33)
                  (n 10) (lo 4/33) (hi 10/11))
  :disable ((frac-alpha-d-in)))

(defrule frac-alpha-d-i<13
  (frac-alpha-d-in *alpha* 13 1/33 10/11)
  :use (:instance frac-alpha-d-in-lemma
                  (alpha *alpha*)
                  (n1 3) (lo1 10/33) (hi1 20/33)
                  (n2 10) (lo2 4/33) (hi2 10/11)
                  (n 13) (lo 1/33) (hi 10/11))
  :disable ((frac-alpha-d-in)))

(defrule frac-alpha-d-i<23
  (frac-alpha-d-in *alpha* 23 1/33 31/33)
  :use (:instance frac-alpha-d-in-lemma
                  (alpha *alpha*)
                  (n1 13) (lo1 1/33) (hi1 10/11)
                  (n2 10) (lo2 4/33) (hi2 10/11)
                  (n 23) (lo 1/33) (hi 31/33))
  :disable ((frac-alpha-d-in)))

(defrule frac-alpha-d-i<33
  (frac-alpha-d-in *alpha* 33 1/33 32/33)
  :use (:instance frac-alpha-d-in-lemma
                  (alpha *alpha*)
                  (n1 23) (lo1 1/33) (hi1 31/33)
                  (n2 10) (lo2 4/33) (hi2 10/11)
                  (n 33) (lo 1/33) (hi 32/33))
  :disable ((frac-alpha-d-in)))

(acl2::with-arith5-help
 (defrule frac-alpha-d-thm
   (implies (natp i)
            (let ((frac (frac (* *alpha* i))))
             (implies (not (= frac 0))
                      (and (<= 1/33 frac)
                           (<= frac 32/33)))))
   :use (:instance lemma
                   (i (floor i 33))
                   (j (mod i 33)))
   :prep-lemmas
   ((defrule lemma
      (implies (and (natp i)
                    (natp j)
                    (< j 33))
               (let* ((k (+ (* i 33) j))
                      (frac (frac (* *alpha* k))))
                 (implies (not (= frac 0))
                          (and (<= 1/33 frac)
                               (<= frac 32/33)))))
      :disable ((frac-alpha-d-in))
      :expand (frac-alpha-d *alpha* j)
      :use ((:instance frac-alpha-d-i<33)
            (:instance frac-alpha-d-in-necc
                       (alpha *alpha*)
                       (i j)
                       (n 33)
                       (lo 1/33)
                       (hi 32/33))
            (:instance frac-+
                       (x (* *alpha* i 33))
                       (y (* *alpha* j))))))))

