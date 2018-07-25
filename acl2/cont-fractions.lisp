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
  (defrule frac-alpha-d-0
    (equal (frac-alpha-d alpha 0) 0))
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

(acl2::with-arith5-help
 (defruled frac-alpha-d-periodic
   (implies (and (= (frac-alpha-d alpha period) 0)
                 (posp period)
                 (natp i))
            (equal (frac-alpha-d alpha (* i period)) 0))
   :induct (sub1-induction i)
   :hints (("subgoal *1/2" :use (:instance frac-alpha-d-+
                                           (d1 (* period (1- i)))
                                           (d2 period)))
           ("subgoal *1/1" :expand (frac-alpha-d alpha 0)))))

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

(define frac-alpha-d-nonzero-in
  :long "for all i in [1,n) (frac(alpha*i)=0 \/ frac(alpha*i) in [lo,hi])"
  ((alpha pos-rationalp)
   (n posp)
   (lo rationalp)
   (hi rationalp))
  :returns (yes booleanp)
  (or (not (integerp n))
      (<= n 1)
      (let ((frac (frac-alpha-d alpha (1- n))))
        (and (or (= frac 0)
                 (and (<= (rfix lo) frac)
                      (<= frac (rfix hi))))
             (frac-alpha-d-nonzero-in alpha (1- n) lo hi))))
  ///
  (fty::deffixequiv frac-alpha-d-nonzero-in
                    :hints (("goal" :in-theory (enable acl2::pos-fix))))
  (defrule frac-alpha-d-nonzeor-in-dummy
    (frac-alpha-d-nonzero-in alpha n 0 1))
  (defruled frac-alpha-d-nonzero-in-when-frac-alpha-d-in
    (implies (and (frac-alpha-d-in alpha n2 lo hi)
                  (<= (acl2::pos-fix n) (acl2::pos-fix n2)))
             (frac-alpha-d-nonzero-in alpha n lo hi))
    :enable acl2::pos-fix
    :induct (frac-alpha-d-nonzero-in alpha n lo hi)
    :hints (("subgoal *1/4" :use (:instance frac-alpha-d-in-necc
                                            (n n2)
                                            (i (1- (acl2::pos-fix n)))))))
  (acl2::with-arith5-help
   (defruled frac-alpha-d-nonzero-in-when-periodic
     (implies (and (frac-alpha-d-in alpha n2 lo hi)
                   (= (frac-alpha-d alpha n2) 0)
                   (posp n2)
                   (posp n))
              (frac-alpha-d-nonzero-in alpha n lo hi))
     :induct (frac-alpha-d-nonzero-in alpha n lo hi)
     :hints
     (("subgoal *1/4"
       :cases ((= 0 (mod (1- n) n2))
               (< 0 (mod (1- n) n2)))
       :use (:instance frac-alpha-d-periodic
                       (period n2)
                       (i (floor (1- n) n2))))
      ("subgoal *1/4.1" :use ((:instance frac-alpha-d-+
                                         (d1 (* n2 (floor (1- n) n2)))
                                         (d2 (mod (1- n) n2)))
                              (:instance frac-alpha-d-in-necc
                                         (n n2)
                                         (i (mod (1- n) n2))))))))
  (defruled frac-alpha-d-nonzero-in-monotonic-by-lo
    (implies (and (frac-alpha-d-nonzero-in alpha n lo2 hi)
                  (<= (rfix lo) (rfix lo2)))
             (frac-alpha-d-nonzero-in alpha n lo hi)))
  (defruled frac-alpha-d-nonzero-in-monotonic-by-hi
    (implies (and (frac-alpha-d-nonzero-in alpha n lo hi2)
                  (<= (rfix hi2) (rfix hi)))
             (frac-alpha-d-nonzero-in alpha n lo hi)))
  (defruled frac-alpha-d-nonzero-in-monotonic-by-lo-hi
    (implies (and (frac-alpha-d-nonzero-in alpha n lo2 hi2)
                  (<= (rfix lo) (rfix lo2))
                  (<= (rfix hi2) (rfix hi)))
             (frac-alpha-d-nonzero-in alpha n lo hi)))
  (defruled frac-alpha-d-nonzero-in-monotonic-by-hi
    (implies (and (frac-alpha-d-nonzero-in alpha n lo hi2)
                  (<= (rfix hi2) (rfix hi)))
             (frac-alpha-d-nonzero-in alpha n lo hi)))
  (defruled frac-alpha-d-nonzero-in-necc
     (let ((frac (frac-alpha-d alpha i)))
       (implies (and (frac-alpha-d-nonzero-in alpha n lo hi)
                     (posp i)
                     (< i (acl2::pos-fix n))
                     (not (= frac 0)))
                (and (<= (rfix lo) frac)
                     (<= frac (rfix hi)))))
     :enable acl2::pos-fix
     :induct (frac-alpha-d-nonzero-in alpha n lo hi)))

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
    (a (fl (/ (- 1 prev-frac) cur-frac))))
   (implies
    (and (posp a)
         (frac-alpha-d-in alpha cur-den (+ cur-frac (- 1 prev-frac)) prev-frac)
         (posp prev-den)
         (posp cur-den)
         (<= prev-den cur-den)
         (<= cur-frac prev-frac))
    (frac-alpha-d-in
     alpha
     (+ prev-den (* a cur-den))
     cur-frac
     (+ prev-frac (* (1- a) cur-frac)))))
  :use ((:instance frac-alpha-d-even
                   (i (1- (fl (/ (- 1 (frac-alpha-d alpha prev-den))
                                 (frac-alpha-d alpha cur-den))))))
        (:instance fl-def
                   (x (/ (- 1 (frac-alpha-d alpha prev-den))
                         (frac-alpha-d alpha cur-den)))))))

(acl2::with-arith5-help
 (defruled frac-alpha-d-start
   (acl2::b*
    ((frac (frac-alpha-d alpha 1))
     (a1 (fl (/ frac))))
    (frac-alpha-d-in alpha a1 frac (* (1- a1) frac)))
   :enable frac-alpha-d-in
   :cases ((<= 2 (fl (/ (frac-alpha-d alpha 1))))
           (= 1 (fl (/ (frac-alpha-d alpha 1))))
           (= 0 (fl (/ (frac-alpha-d alpha 1)))))
   :hints
   (("subgoal 3" :use
     ((:instance frac-alpha-d-even-corr
                 (prev-den 1)
                 (cur-den 1))
      (:instance fl+int-rewrite
                 (n -1)
                 (x (/ (frac-alpha-d alpha 1)))))))))

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
    (a (fl (/ prev-frac (- 1 cur-frac)))))
   (implies
    (and (posp a)
         (frac-alpha-d-in alpha cur-den prev-frac (- cur-frac prev-frac))
         (posp prev-den)
         (posp cur-den)
         (<= prev-den cur-den)
         (<= prev-frac cur-frac))
    (frac-alpha-d-in
     alpha
     (+ prev-den (* a cur-den))
     (- prev-frac (* (1- a) (- 1 cur-frac)))
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
  :returns (mv (cur-den posp :rule-classes :type-prescription)
               (prev-den posp :rule-classes :type-prescription)
               (lo rationalp :rule-classes :type-prescription)
               (hi rationalp :rule-classes :type-prescription))
  :measure (nfix (- (1+ (acl2::pos-fix max-den))
                    (acl2::pos-fix cur-den)))
  (acl2::b*
   ((cur-den (acl2::pos-fix cur-den))
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
    ((unless (and (<= prev-den cur-den)
                  (<= cur-den max-den)
                  (< 0 cur-frac)
                  (if odd
                      (<= prev-frac cur-frac)
                    (<= cur-frac prev-frac))))
     (mv cur-den prev-den lo hi))
    (a-pre (if odd
               (/ prev-frac (- 1 cur-frac))
             (/ (- 1 prev-frac) cur-frac)))
    (a (fl a-pre))
    ((unless (posp a))
     (mv cur-den prev-den lo hi)))
   (frac-alpha-d-bound-aux alpha (+ prev-den (* a cur-den)) cur-den (not odd) max-den))
  ///
  (fty::deffixequiv frac-alpha-d-bound-aux)))

(acl2::with-arith5-help
 (defrule frac-alpha-d-bound-aux-correct
  (acl2::b*
   ((cur-frac (frac-alpha-d alpha cur-den))
    (prev-frac (frac-alpha-d alpha prev-den))
    (cur-lo (if odd
                prev-frac
              (+ cur-frac (- 1 prev-frac))))
    (cur-hi (if odd
                (- (if (= cur-frac 0) 1 cur-frac) prev-frac)
              prev-frac))
    ((mv new-cur-den ?new-prev-den lo hi)
     (frac-alpha-d-bound-aux alpha cur-den prev-den odd max-den)))
   (implies
    (and (frac-alpha-d-in alpha cur-den cur-lo cur-hi)
         (posp prev-den)
         (posp cur-den))
    (frac-alpha-d-in alpha new-cur-den lo hi)))
  :induct (frac-alpha-d-bound-aux alpha cur-den prev-den odd max-den)
  :enable (frac-alpha-d-bound-aux)
  :disable frac-alpha-d-+
  :hints (("subgoal *1/1" :cases (odd) :do-not-induct t)
          ("subgoal *1/1.2" :use frac-alpha-d-even-corr
           :cases ((< (* (frac-alpha-d alpha cur-den)
                         (fl (/ (- 1 (frac-alpha-d alpha prev-den))
                                (frac-alpha-d alpha cur-den))))
                      (- 1 (frac-alpha-d alpha prev-den)))
                   (= (* (frac-alpha-d alpha cur-den)
                         (fl (/ (- 1 (frac-alpha-d alpha prev-den))
                                (frac-alpha-d alpha cur-den))))
                      (- 1 (frac-alpha-d alpha prev-den)))))
          ("subgoal *1/1.2.3" :use
           (:instance lemma
                      (x (- 1 (frac-alpha-d alpha prev-den)))
                      (y (frac-alpha-d alpha cur-den))))
          ("subgoal *1/1.1" :use frac-alpha-d-odd-corr
           :cases ((< (* (- 1 (frac-alpha-d alpha cur-den))
                         (fl (/ (frac-alpha-d alpha prev-den)
                                (- 1 (frac-alpha-d alpha cur-den)))))
                      (frac-alpha-d alpha prev-den))
                   (= (* (- 1 (frac-alpha-d alpha cur-den))
                         (fl (/ (frac-alpha-d alpha prev-den)
                                (- 1 (frac-alpha-d alpha cur-den)))))
                      (frac-alpha-d alpha prev-den))))
          ("subgoal *1/1.1.3" :use
           (:instance lemma
                      (x (frac-alpha-d alpha prev-den))
                      (y (- 1 (frac-alpha-d alpha cur-den))))))
  :prep-lemmas
  ((acl2::with-arith5-nonlinear-help
    (defruled lemma
      (implies (and (rationalp x)
                    (rationalp y)
                   (< 0 y))
               (<= (* y (fl (/ x y))) x)))))))

(acl2::with-arith5-nonlinear-help
 (define frac-alpha-d-bound
  ((alpha pos-rationalp)
   (max-den posp))
  :returns (mv (cur-den posp :rule-classes :type-prescription)
               (prev-den natp :rule-classes :type-prescription)
               (lo rationalp :rule-classes :type-prescription)
               (hi rationalp :rule-classes :type-prescription))
  (acl2::b*
   ((frac (frac-alpha-d alpha 1)))
   (if (= frac 0)
       (mv 1 0 1 0)
     (frac-alpha-d-bound-aux alpha (fl (/ frac)) 1 t max-den)))
  ///
  (fty::deffixequiv frac-alpha-d-bound)))

(acl2::with-arith5-nonlinear-help
 (defrule frac-alpha-d-bound-correct
  (acl2::b* (((mv cur-den ?prev-den lo hi) (frac-alpha-d-bound alpha max-den)))
            (frac-alpha-d-in alpha cur-den lo hi))
 :enable frac-alpha-d-bound
 :use (:instance frac-alpha-d-bound-aux-correct
                 (cur-den (fl (/ (frac-alpha-d alpha 1))))
                 (prev-den 1)
                 (odd t))
 :cases ((= 0 (frac-alpha-d alpha 1))
         (< 1/2 (frac-alpha-d alpha 1)))
 :hints
 (("subgoal 3" :use frac-alpha-d-start
   :cases ((< (* (frac-alpha-d alpha 1)
                 (fl (/ (frac-alpha-d alpha 1))))
              1)
           (= (* (frac-alpha-d alpha 1)
                 (fl (/ (frac-alpha-d alpha 1))))
              1)))
  ("subgoal 3.2" :use (:instance frac-alpha-d-arith-progression-up
                                 (prev-den 1)
                                 (cur-den 1)
                                 (i (1- (fl (/ (frac-alpha-d alpha 1)))))))
  ("subgoal 3.1" :use (:instance frac-alpha-d-arith-progression-up=
                                 (prev-den 1)
                                 (cur-den 1)
                                 (i (1- (fl (/ (frac-alpha-d alpha 1)))))))
  ("subgoal 2" :expand (frac-alpha-d-in alpha 1 1 0))
  ("subgoal 1" :cases ((= (fl (/ (frac-alpha-d alpha 1))) 1))
   :expand (frac-alpha-d-in alpha 1 (frac-alpha-d alpha 1) 0)))))

(define frac-alpha-d-nonzero-bound
  ((alpha pos-rationalp)
   (max-den posp))
  :returns (mv (lo rationalp :rule-classes :type-prescription)
               (hi rationalp :rule-classes :type-prescription))
  (acl2::b*
   (((mv cur-den ?prev-den lo hi)
     (frac-alpha-d-bound alpha max-den)))
   (if (or (< (acl2::pos-fix max-den) cur-den)
           (= (frac-alpha-d alpha cur-den) 0))
       (mv lo hi)
     (mv 0 1)))
  ///
  (fty::deffixequiv frac-alpha-d-nonzero-bound)
  (defrule frac-alpha-d-nonzero-bound-correct
    (acl2::b*
     (((mv lo hi) (frac-alpha-d-nonzero-bound alpha max-den)))
     (implies (posp max-den)
              (frac-alpha-d-nonzero-in alpha (1+ max-den) lo hi)))
    :cases
    ((< (acl2::pos-fix max-den)
        (mv-nth 0 (frac-alpha-d-bound alpha max-den)))
     (= (frac-alpha-d alpha (mv-nth 0 (frac-alpha-d-bound alpha max-den)))
        0))
    :hints
    (("subgoal 2" :use
      (:instance frac-alpha-d-nonzero-in-when-frac-alpha-d-in
                 (n2 (mv-nth 0 (frac-alpha-d-bound alpha max-den)))
                 (n (1+ max-den))
                 (lo (mv-nth 2 (frac-alpha-d-bound alpha max-den)))
                 (hi (mv-nth 3 (frac-alpha-d-bound alpha max-den)))))
     ("subgoal 1" :use
      (:instance frac-alpha-d-nonzero-in-when-periodic
                 (n2 (mv-nth 0 (frac-alpha-d-bound alpha max-den)))
                 (n (1+ max-den))
                 (lo (mv-nth 2 (frac-alpha-d-bound alpha max-den)))
                 (hi (mv-nth 3 (frac-alpha-d-bound alpha max-den))))))))

(acl2::with-arith5-help
 (define frac-alpha-d-nonzero-bound-f-aux
   ((f formatp)
    (q integerp))
   :returns (mv (lo rationalp :rule-classes :type-prescription)
                (hi rationalp :rule-classes :type-prescription))
   :measure (nfix (- (1+ (ifix q)) (Qmin f)))
   :verify-guards nil
   (acl2::b*
    ((q (ifix q))
     ((unless (<= (Qmin f) q)) (mv 1 0))
     (ulp2 (expt 2 q))
     (r (1- (ordD ulp2)))
     (ulpD (expt (D) r))
     (alpha (/ ulp2 ulpD))
     (CMax (+ (expt 2 (1+ (P f))) 2))
     ((mv lo1 hi1) (frac-alpha-d-nonzero-bound alpha CMax))
     ((mv lo2 hi2) (frac-alpha-d-nonzero-bound-f-aux f (1- q))))
    (mv (min lo1 lo2) (max hi1 hi2)))
   ///
   (fty::deffixequiv frac-alpha-d-nonzero-bound-f-aux)
   (verify-guards frac-alpha-d-nonzero-bound-f-aux)
   (defrule frac-alpha-d-nonzero-bound-f-aux-correct
     (acl2::b*
      ((ulp2 (expt 2 q))
       (r (1- (ordD ulp2)))
       (ulpD (expt (D) r))
       (alpha (/ ulp2 ulpD))
       (CMax1 (+ (expt 2 (1+ (P f))) 3))
       ((mv lo hi) (frac-alpha-d-nonzero-bound-f-aux f qmax)))
      (implies (and (integerp qmax)
                    (integerp q)
                    (<= (Qmin f) q)
                    (<= q qmax))
               (frac-alpha-d-nonzero-in alpha Cmax1 lo hi)))
     :induct (frac-alpha-d-nonzero-bound-f-aux f qmax)
     :enable frac-alpha-d-nonzero-bound-f-aux
     :hints
     (("subgoal *1/1" :cases ((< qmax q) (= qmax q) (> qmax q)))
      ("subgoal *1/1.2" :use
       ((:instance frac-alpha-d-nonzero-bound-correct
                   (alpha (/ (expt 2 q) (expt (D) (1- (ordD (expt 2 q))))))
                   (max-den (+ (expt 2 (1+ (P f))) 2)))
        (:instance frac-alpha-d-nonzero-in-monotonic-by-lo-hi
                   (alpha (/ (expt 2 q) (expt (D) (1- (ordD (expt 2 q))))))
                   (n (+ (expt 2 (1+ (P f))) 3))
                   (lo2 (mv-nth 0 (frac-alpha-d-nonzero-bound
                                   (/ (expt 2 q)
                                      (expt (D) (1- (ordD (expt 2 q)))))
                                   (+ (expt 2 (1+ (P f))) 2))))
                   (hi2 (mv-nth 1 (frac-alpha-d-nonzero-bound
                                   (/ (expt 2 q)
                                      (expt (D) (1- (ordD (expt 2 q)))))
                                   (+ (expt 2 (1+ (P f))) 2))))
                   (lo (mv-nth 0 (frac-alpha-d-nonzero-bound-f-aux f q)))
                   (hi (mv-nth 1 (frac-alpha-d-nonzero-bound-f-aux f q)))))
       :expand (frac-alpha-d-nonzero-bound-f-aux f q))
      ("subgoal *1/1.1" :use
       (:instance frac-alpha-d-nonzero-in-monotonic-by-lo-hi
                  (alpha (/ (expt 2 q) (expt (D) (1- (ordD (expt 2 q))))))
                  (n (+ (expt 2 (1+ (P f))) 3))
                  (lo2 (mv-nth 0 (frac-alpha-d-nonzero-bound-f-aux f (1- qmax))))
                  (hi2 (mv-nth 1 (frac-alpha-d-nonzero-bound-f-aux f (1- qmax))))
                  (lo (mv-nth 0 (frac-alpha-d-nonzero-bound-f-aux f qmax)))
                  (hi (mv-nth 1 (frac-alpha-d-nonzero-bound-f-aux f qmax)))))))))

(define frac-alpha-d-nonzero-bound-f
  ((f formatp))
  :returns (mv (lo rationalp :rule-classes :type-prescription)
               (hi rationalp :rule-classes :type-prescription))
  (frac-alpha-d-nonzero-bound-f-aux f (Qmax f))
  ///
  (fty::deffixequiv frac-alpha-d-nonzero-bound-f)
  (acl2::with-arith5-help
   (defruled frac-alpha-d-nonzero-bound-f-correct
     (acl2::b*
      ((ulp2 (expt 2 q))
       (r (1- (ordD ulp2)))
       (ulpD (expt (D) r))
       (alpha (/ ulp2 ulpD))
       (CMax (+ (expt 2 (1+ (P f))) 2))
       ((mv lo hi) (frac-alpha-d-nonzero-bound-f f))
       (frac (frac-alpha-d alpha c)))
      (implies (and (integerp q)
                   (<= (Qmin f) q)
                   (<= q (Qmax f))
                   (natp c)
                   (<= c CMax)
                   (not (= frac 0)))
               (and (<= lo frac)
                    (<= frac hi))))
     :use
     ((:instance frac-alpha-d-nonzero-in-necc
                 (alpha (/ (expt 2 q) (expt (D) (1- (ordD (expt 2 q))))))
                 (n (+ (expt 2 (1+ (P f))) 3))
                 (i c)
                 (lo (mv-nth 0 (frac-alpha-d-nonzero-bound-f f)))
                 (hi (mv-nth 1 (frac-alpha-d-nonzero-bound-f f))))
      (:instance frac-alpha-d-nonzero-bound-f-aux-correct
                 (qmax (Qmax f)))))))

(defruled frac-alpha-d-nonzero-bound-hp-correct
  (acl2::b*
   ((f (hp))
    (lo 1/65536)
    (hi (- 1 1/65536))
    (ulp2 (expt 2 q))
    (r (1- (ordD ulp2)))
    (ulpD (expt (D) r))
    (alpha (/ ulp2 ulpD))
    (CMax (+ (expt 2 (1+ (P f))) 2))
    (frac (frac-alpha-d alpha c)))
   (implies (and (integerp q)
                 (<= (Qmin f) q)
                 (<= q (Qmax f))
                 (natp c)
                 (<= c CMax)
                 (not (= frac 0)))
            (and (<= lo frac)
                 (<= frac hi))))
  :enable hp
  :use (:instance frac-alpha-d-nonzero-bound-f-correct (f (hp))))

(defruled frac-alpha-d-nonzero-bound-sp-correct
  (acl2::b*
   ((f (sp))
    (lo 43/152587890625)
    (hi (- 1 47/152587890625))
    (ulp2 (expt 2 q))
    (r (1- (ordD ulp2)))
    (ulpD (expt (D) r))
    (alpha (/ ulp2 ulpD))
    (CMax (+ (expt 2 (1+ (P f))) 2))
    (frac (frac-alpha-d alpha c)))
   (implies (and (integerp q)
                 (<= (Qmin f) q)
                 (<= q (Qmax f))
                 (natp c)
                 (<= c CMax)
                 (not (= frac 0)))
            (and (<= lo frac)
                 (<= frac hi))))
  :enable sp
  :use (:instance frac-alpha-d-nonzero-bound-f-correct (f (sp))))

(defruled frac-alpha-d-nonzero-bound-dp-correct
  (acl2::b*
   ((f (dp))
    (lo 1323359619378521/17763568394002504646778106689453125)
    (hi (- 1 1857975741265209/17763568394002504646778106689453125))
    (ulp2 (expt 2 q))
    (r (1- (ordD ulp2)))
    (ulpD (expt (D) r))
    (alpha (/ ulp2 ulpD))
    (CMax (+ (expt 2 (1+ (P f))) 2))
    (frac (frac-alpha-d alpha c)))
   (implies (and (integerp q)
                 (<= (Qmin f) q)
                 (<= q (Qmax f))
                 (natp c)
                 (<= c CMax)
                 (not (= frac 0)))
            (and (<= lo frac)
                 (<= frac hi))))
  :enable dp
  :use (:instance frac-alpha-d-nonzero-bound-f-correct (f (dp))))

(defruled frac-alpha-d-nonzero-bound-hp-correct-corr
  (acl2::b*
   ((f (hp))
    (lo (expt 2 -16))
    (hi (- 1 (expt 2 -16)))
    (ulp2 (expt 2 q))
    (r (1- (ordD ulp2)))
    (ulpD (expt (D) r))
    (alpha (/ ulp2 ulpD))
    (CMax (+ (expt 2 (1+ (P f))) 2))
    (frac (frac-alpha-d alpha c)))
   (implies (and (integerp q)
                 (<= (Qmin f) q)
                 (<= q (Qmax f))
                 (natp c)
                 (<= c CMax)
                 (not (= frac 0)))
            (and (<= lo frac)
                 (<= frac hi))))
  :use frac-alpha-d-nonzero-bound-hp-correct)

(defruled frac-alpha-d-nonzero-bound-sp-correct-corr
  (acl2::b*
   ((f (sp))
    (lo (expt 2 -32))
    (hi (- 1 (expt 2 -32)))
    (ulp2 (expt 2 q))
    (r (1- (ordD ulp2)))
    (ulpD (expt (D) r))
    (alpha (/ ulp2 ulpD))
    (CMax (+ (expt 2 (1+ (P f))) 2))
    (frac (frac-alpha-d alpha c)))
   (implies (and (integerp q)
                 (<= (Qmin f) q)
                 (<= q (Qmax f))
                 (natp c)
                 (<= c CMax)
                 (not (= frac 0)))
            (and (< lo frac)
                 (< frac hi))))
  :use frac-alpha-d-nonzero-bound-sp-correct)

(defruled frac-alpha-d-nonzero-bound-dp-correct-corr
  (acl2::b*
   ((f (dp))
    (lo (expt 2 -64))
    (hi (- 1 (expt 2 -64)))
    (ulp2 (expt 2 q))
    (r (1- (ordD ulp2)))
    (ulpD (expt (D) r))
    (alpha (/ ulp2 ulpD))
    (CMax (+ (expt 2 (1+ (P f))) 2))
    (frac (frac-alpha-d alpha c)))
   (implies (and (integerp q)
                 (<= (Qmin f) q)
                 (<= q (Qmax f))
                 (natp c)
                 (<= c CMax)
                 (not (= frac 0)))
            (and (< lo frac)
                 (< frac hi))))
  :use frac-alpha-d-nonzero-bound-dp-correct)

