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

(define frac-alpha-in
  :long "for all i in [1,n) frac(alpha*i) in [lo,hi]"
  ((alpha pos-rationalp)
   (n posp)
   (lo rationalp)
   (hi rationalp))
  :returns (yes booleanp)
  (or (not (integerp n))
      (<= n 1)
      (let ((frac (frac (* (pos-rational-fix alpha) (1- n)))))
        (and (<= (rfix lo) frac)
             (<= frac (rfix hi))
             (frac-alpha-in alpha (1- n) lo hi))))
  ///
  (fty::deffixequiv frac-alpha-in
                    :hints (("goal" :in-theory (enable acl2::pos-fix))))
  (acl2::with-arith5-help
   (defruled frac-alpha-in-necc
     (implies (and (frac-alpha-in alpha n lo hi)
                   (posp i)
                   (< i (nfix n)))
              (let ((frac (frac (* (pos-rational-fix alpha) i))))
                (and (<= (rfix lo) frac)
                     (<= frac (rfix hi))))))))

(acl2::with-arith5-nonlinear-help
 (define frac-alpha-bound-aux
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
   ((alpha (pos-rational-fix alpha))
    (cur-den (acl2::pos-fix cur-den))
    (prev-den (acl2::pos-fix prev-den))
    (max-den (acl2::pos-fix max-den))
    (cur-frac (frac (* alpha cur-den)))
    (prev-frac (frac (* alpha prev-den)))
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
               (< max-den cur-den)))
     (mv cur-den lo hi)))
   (frac-alpha-bound-aux alpha (+ prev-den (* q cur-den)) cur-den (not odd) max-den))
  ///
  (fty::deffixequiv frac-alpha-bound-aux)))

(acl2::with-arith5-nonlinear-help
 (define frac-alpha-bound
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
          (frac-alpha-bound-aux alpha (fl (/ frac)) 1 t max-den))
         ((> frac 1/2)
          (frac-alpha-bound-aux alpha (fl (/ (- 1 frac))) 1 nil max-den))
         (t (mv 2 1/2 1/2))))
  :guard-hints
  (("goal" :use
    (:instance n<=fl-linear
               (n 2)
               (x (/ (- 1 (frac (pos-rational-fix alpha))))))))
  ///
  (fty::deffixequiv frac-alpha-bound)))

(define frac-alpha-bound-q
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
   (frac-alpha-bound alpha max-den))
  ///
  (fty::deffixequiv frac-alpha-bound-q))

(acl2::with-arith5-help
 (define frac-alpha-bound-f
   ((f formatp)
    (q integerp)
    (acc true-listp))
   :measure (nfix (- (1+ (ifix q)) (Qmin f)))
   (acl2::b*
    ((q (ifix q))
     ((unless (<= (Qmin f) q)) acc)
     ((mv den lo hi) (frac-alpha-bound-q q (+ (expt 2 (1+ (P f))) 2))))
    (frac-alpha-bound-f
     f
     (1- q)
     (cons (list q den lo hi) acc)))))

(defconst *dp-bounds* (frac-alpha-bound-f (dp) (- 1023 52) nil))

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
  (equal (frac-alpha-bound *alpha* 1) (list 3 10/33 20/33))
  (equal (frac-alpha-bound *alpha* 3) (list 10 4/33 10/11))
  (equal (frac-alpha-bound *alpha* 10) (list 33 1/33 32/33))))

(defrule frac-alpha-i<2
  (implies (and (posp i)
                (< i 2))
           (let ((frac (frac (* *alpha* i))))
             (and (<= 10/33 frac)
                  (<= frac 10/33)))))

(defruled frac-alpha-i<3
  (implies (and (posp i)
                (< i 3))
           (let ((frac (frac (* *alpha* i))))
             (and (<= 10/33 frac)
                  (<= frac 20/33))))
  :cases ((< i 2)
          (= i 2)
          (> i 2)))

(defruled frac-alpha-i<4
  (implies (and (posp i)
                (< i 4))
           (let ((frac (frac (* *alpha* i))))
             (and (<= 10/33 frac)
                  (<= frac 10/11))))
  :cases ((< i 3)
          (= i 3)
          (> i 3))
  :hints (("subgoal 3" :use frac-alpha-i<3)))

(acl2::with-arith5-help
 (defruled frac-alpha-i<7
   (implies (and (posp i)
                 (< i 7))
            (let ((frac (frac (* *alpha* i))))
              (and (<= 7/33 frac)
                   (<= frac 10/11))))
   :cases ((< i 4)
           (= i 4)
           (> i 4))
   :hints (("subgoal 3" :use frac-alpha-i<4)
           ("subgoal 1" :use ((:instance frac-alpha-i<3
                                         (i (- i 4)))
                              (:instance frac-+
                                         (x (* *alpha* 4))
                                         (y (* *alpha* (- i 4)))))))))

(acl2::with-arith5-help
 (defruled frac-alpha-i<10
   (implies (and (posp i)
                 (< i 10))
            (let ((frac (frac (* *alpha* i))))
              (and (<= 4/33 frac)
                   (<= frac 10/11))))
   :cases ((< i 7)
           (= i 7)
           (> i 7))
   :hints (("subgoal 3" :use frac-alpha-i<7)
           ("subgoal 1" :use ((:instance frac-alpha-i<3
                                         (i (- i 7)))
                              (:instance frac-+
                                         (x (* *alpha* 7))
                                         (y (* *alpha* (- i 7)))))))))

(acl2::with-arith5-help
 (defruled frac-alpha-i<13
   (implies (and (posp i)
                 (< i 13))
            (let ((frac (frac (* *alpha* i))))
              (and (<= 1/33 frac)
                   (<= frac 10/11))))
   :cases ((< i 10)
           (= i 10)
           (> i 10))
   :hints (("subgoal 3" :use frac-alpha-i<10)
           ("subgoal 1" :use ((:instance frac-alpha-i<3
                                         (i (- i 10)))
                              (:instance frac-+
                                         (x (* *alpha* 10))
                                         (y (* *alpha* (- i 10)))))))))

(acl2::with-arith5-help
 (defruled frac-alpha-i<23
  (implies (and (posp i)
                (< i 23))
           (let ((frac (frac (* *alpha* i))))
             (and (<= 1/33 frac)
                  (<= frac 31/33))))
  :cases ((< i 13)
          (= i 13)
          (> i 13))
  :hints (("subgoal 3" :use frac-alpha-i<13)
          ("subgoal 1" :use ((:instance frac-alpha-i<10
                                        (i (- i 13)))
                             (:instance frac-+
                                        (x (* *alpha* 13))
                                        (y (* *alpha* (- i 13)))))))))

(acl2::with-arith5-help
 (defruled frac-alpha-i<33
  (implies (and (posp i)
                (< i 33))
           (let ((frac (frac (* *alpha* i))))
             (and (<= 1/33 frac)
                  (<= frac 32/33))))
  :cases ((< i 23)
          (= i 23)
          (> i 23))
  :hints (("subgoal 3" :use frac-alpha-i<23)
          ("subgoal 1" :use ((:instance frac-alpha-i<10
                                        (i (- i 23)))
                             (:instance frac-+
                                        (x (* *alpha* 23))
                                        (y (* *alpha* (- i 23)))))))))

(acl2::with-arith5-help
 (defrule frac-alpha-thm
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
      :use ((:instance frac-alpha-i<33
                       (i j))
            (:instance frac-+
                       (x (* *alpha* i 33))
                       (y (* *alpha* j))))))))

