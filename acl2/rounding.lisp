(in-package "RTL")
(include-book "section5")

;(local (include-book "rtl/rel11/support/basic" :dir :system))
(local (include-book "rtl/rel11/support/float" :dir :system))
(local (include-book "rtl/rel11/support/round" :dir :system))
(local (acl2::allow-arith5-help))

; enumerate nonnegative values of format f

(defrule radixp-compound-recognizer
  (equal (radixp b)
         (and (integerp b) (< 1 b)))
  :rule-classes :compound-recognizer
  :enable radixp)

(define radix-fix
  ((b radixp))
  :returns (b-fixed radixp :rule-classes ())
  (if (radixp b) b 2)
  ///
  (defrule radix-fix-when-radixp
    (implies (radixp x)
             (equal (radix-fix x) x)))
  (fty::deffixtype radix
    :pred radixp
    :fix radix-fix
    :equiv radix-equiv
    :define t)
  (in-theory (disable radix-equiv)))

(acl2::with-arith5-help
 (define enum-drange
   ((p posp)
    (b radixp))
   :returns (emum-drange posp :rule-classes ())
   (acl2::b*
    ((p (acl2::pos-fix p))
     (b (radix-fix b)))
    (expt b (- p 1)))
   ///
   (fty::deffixequiv enum-drange)))

(acl2::with-arith5-help
 (define enum-nrange
   ((p posp)
    (b radixp))
   :returns (emum-nrange posp :rule-classes :type-prescription)
   (acl2::b*
    ((p (acl2::pos-fix p))
     (b (radix-fix b)))
    (- (expt b p) (expt b (- p 1))))
   ///
   (fty::deffixequiv enum-nrange)))

(acl2::with-arith5-help
 (define enum-q
   ((n natp)
    (p posp)
    (qmin integerp)
    (b radixp))
   :returns (q integerp :rule-classes ())
   (acl2::b*
    ((n (nfix n))
     (qmin (ifix qmin))
     (drange (enum-drange p b))
     (nrange (enum-nrange p b)))
    (if (< n drange)
        qmin
      (+ qmin (fl (/ (- n drange) nrange)))))
   ///
   (fty::deffixequiv enum-q)
   (defrule enum-q-lower-bound
     (>= (enum-q n p qmin b) (ifix qmin))
     :use (:instance fl-monotone-linear
                     (x 0)
                     (y (/ (- (nfix n) (enum-drange p b)) (enum-nrange p b))))
     :rule-classes :linear)
   (acl2::with-arith5-nonlinear-help
    (defrule enum-q-when-n<drange+nrange
      (implies (< (nfix n) (+ (enum-drange p b) (enum-nrange p b)))
               (equal (enum-q n p qmin b) (ifix qmin)))
      :use (:instance fl-unique
                      (x (/ (- (nfix n) (enum-drange p b)) (enum-nrange p b)))
                      (n 0))))
   (acl2::with-arith5-nonlinear-help
    (defrule enum-q-lower-bound-when-n>=drange+nrange
      (implies (>= (nfix n) (+ (enum-drange p b) (enum-nrange p b)))
               (>= (enum-q n p qmin b) (1+ (ifix qmin))))
      :rule-classes :linear
      :use (:instance fl-monotone-linear
                      (x 1)
                      (y (/ (- (nfix n) (enum-drange p b))
                            (enum-nrange p b))))))
   (defruled enum-q-next
     (implies (natp n)
              (equal (enum-q (1+ n) p qmin b)
                     (if (and (<= (enum-drange p b) n)
                              (= (mod (- n (enum-drange p b))
                                      (enum-nrange p b))
                                 (1- (enum-nrange p b))))
                         (1+ (enum-q n p qmin b))
                       (enum-q n p qmin b))))
     :use (:instance lemma
                     (n (- n (enum-drange p b)))
                     (nrange (enum-nrange p b)))
     :prep-lemmas
     ((acl2::with-arith5-nonlinear++-help
       (defruled lemma
         (implies (and (natp n)
                       (posp nrange))
                  (equal (fl (/ (1+ n) nrange))
                         (if (= (mod n nrange) (1- nrange))
                             (1+ (fl (/ n nrange)))
                           (fl (/ n nrange)))))
         :enable fl))))
   (defrule enum-q-monotone
     (implies (<= (nfix n1) (nfix n2))
              (<= (enum-q n1 p qmin b) (enum-q n2 p qmin b)))
     :rule-classes ()
     :cases ((<= (enum-drange p b) (nfix n1)))
     :disable enum-q
     :hints
     (("subgoal 1" :in-theory (enable enum-q)
       :use (:instance fl-monotone-linear
                       (x (/ (- (nfix n1) (enum-drange p b))
                             (enum-nrange p b)))
                       (y (/ (- (nfix n2) (enum-drange p b))
                             (enum-nrange p b)))))))))

(acl2::with-arith5-help
 (define enum-c
   ((n natp)
    (p posp)
    (b radixp))
   :returns (c natp :rule-classes ())
   (acl2::b*
    ((n (nfix n))
     (drange (enum-drange p b))
     (nrange (enum-nrange p b)))
    (if (< n drange)
        n
      (+ drange (mod (- n drange) nrange))))
   ///
   (fty::deffixequiv enum-c)
   (defrule enum-c-when-n<drange+nrange
     (implies (< (nfix n) (+ (enum-drange p b) (enum-nrange p b)))
              (equal (enum-c n p b) (nfix n))))
   (defrule enum-c-upper-bound
     (<= (enum-c n p b) (+ -1 (enum-drange p b) (enum-nrange p b)))
     :rule-classes :linear)
   (defrule enum-c-lower-bound-when-normal
     (implies (<= (enum-drange p b) (nfix n))
              (<= (enum-drange p b) (enum-c n p b)))
     :rule-classes :linear)
   (defrule enum-c-type-when-n>=1
     (implies (posp n)
              (posp (enum-c n p b)))
     :rule-classes :type-prescription
     :disable enum-c
     :use enum-c-lower-bound-when-normal)
   (defruled enum-c-next
     (implies (natp n)
              (equal (enum-c (1+ n) p b)
                     (if (and (<= (enum-drange p b) n)
                              (= (mod (- n (enum-drange p b))
                                      (enum-nrange p b))
                                 (1- (enum-nrange p b))))
                         (enum-drange p b)
                       (1+ (enum-c n p b)))))
     :cases ((<= n (+ -2 (enum-drange p b)))
             (=  n (+ -1 (enum-drange p b)))
             (>= n (enum-drange p b)))
     :prep-lemmas
     ((acl2::with-arith5-nonlinear++-help
       (defruled lemma
         (implies (and (natp n)
                       (posp nrange))
                  (equal (mod (1+ n) nrange)
                         (if (= (mod n nrange) (1- nrange))
                             0
                           (1+ (mod n nrange)))))))))
   (defrule expq-enum-c-when-normal
     (implies (and (<= (enum-drange p b) (nfix n))
                   (posp p)
                   (radixp b))
              (equal (expq (enum-c n p b) p b) 0))
     :enable (enum-drange enum-nrange)
     :disable enum-c
     :use (:instance expq-unique
                     (x (enum-c n p b))
                     (n 0)))
   (defrule sigc-enum-c-when-normal
     (implies (and (<= (enum-drange p b) (nfix n))
                   (posp p)
                   (radixp b))
              (equal (sigc (enum-c n p b) p b)
                     (enum-c n p b)))
     :enable (enum-drange enum-nrange)
     :disable enum-c
     :use (:instance sigc-self
                     (x (enum-c n p b))))
   (defrule expq-enum-c-type
     (implies (and (posp p)
                   (radixp b))
              (and (integerp (expq (enum-c n p b) p b))
                   (<= (expq (enum-c n p b) p b) 0)))
     :rule-classes :type-prescription
     :disable enum-c
     :cases ((zp n)
             (<= (enum-drange p b) (nfix n)))
     :hints
     (("subgoal 3" :in-theory (enable enum-drange) :use
       (:instance expq<=
                  (x n)
                  (n -1)))
      ("subgoal 2" :in-theory (enable expq expe))))))

(acl2::with-arith5-help
 (define enum-v
   ((n natp)
    (p posp)
    (qmin integerp)
    (b radixp))
   :returns (v (and (rationalp v) (<= 0 v)) :rule-classes ())
   (* (enum-c n p b) (expt (radix-fix b) (enum-q n p qmin b)))
   ///
   (fty::deffixequiv enum-v :hints (("goal" :in-theory (disable ifix))))
   (defruled enum-v-when-denormal
     (implies (< (nfix n) (enum-drange p b))
              (equal (enum-v n p qmin b)
                     (* (nfix n) (expt (radix-fix b) (ifix qmin))))))
   (defrule enum-v-n=0
     (equal (enum-v 0 p qmin b) 0))
   (acl2::with-arith5-nonlinear-help
    (defrule enum-v-type-n>0
      (implies (posp n)
               (pos-rationalp (enum-v n p qmin b)))
      :rule-classes :type-prescription))
   (defruled expq-enum-v-when-normal
     (implies (and (<= (enum-drange p b) (nfix n))
                   (posp p)
                   (radixp b))
              (equal (expq (enum-v n p qmin b) p b)
                     (enum-q n p qmin b)))
     :use (:instance expq-shift
                     (x (enum-c n p b))
                     (n (enum-q n p qmin b))))
   (defruled sigc-enum-v-when-normal
     (implies (and (<= (enum-drange p b) (nfix n))
                   (posp p)
                   (radixp b))
              (equal (sigc (enum-v n p qmin b) p b)
                     (enum-c n p b)))
     :use (:instance sigc-shift
                     (x (enum-c n p b))
                     (n (enum-q n p qmin b))))
   (defruled enum-q-as-expq-enum-v
     (implies (posp n)
              (equal (enum-q n p qmin b)
                     (max (expq (enum-v n p qmin b)
                                (acl2::pos-fix p)
                                (radix-fix b))
                          (ifix qmin))))
     :disable enum-v
     :cases ((<= (enum-drange p b) n))
     :hints
     (("subgoal 2" :in-theory (enable enum-v-when-denormal enum-drange)
       :use (:instance expq<=
                       (x (* n (expt (radix-fix b) (ifix qmin))))
                       (p (acl2::pos-fix p))
                       (b (radix-fix b))
                       (n (1- (ifix qmin)))))
      ("subgoal 1" :use (:instance expq-enum-v-when-normal
                                   (p (acl2::pos-fix p))
                                   (b (radix-fix b))))))
   (defruled enum-v-next
     (implies (natp n)
              (equal (enum-v (1+ n) p qmin b)
                     (+ (enum-v n p qmin b)
                        (expt (radix-fix b) (enum-q n p qmin b)))))
     :enable (enum-q-next enum-c-next)
     :cases ((and (<= (enum-drange p b) n)
                  (= (mod (- n (enum-drange p b)) (enum-nrange p b))
                     (1- (enum-nrange p b)))))
     :hints (("subgoal 1" :in-theory (enable enum-drange enum-nrange)
              :use lemma))
     :prep-lemmas
     ((defruled lemma
        (implies (and (= (mod (- n (enum-drange p b))
                              (enum-nrange p b))
                         (1- (enum-nrange p b)))
                      (integerp n)
                      (<= (enum-drange p b) n))
                 (equal (enum-c n p b) (+ -1 (enum-drange p b) (enum-nrange p b))))
        :enable enum-c)))
   (defruled enum-v-monotone
     (implies (< (nfix n1) (nfix n2))
              (< (enum-v n1 p qmin b) (enum-v n2 p qmin b)))
     :disable enum-v
     :induct (sub1-induction n2)
     :hints
     (("subgoal *1/2" :cases ((= (nfix n2) (1+ (nfix n1)))
                              (> (nfix n2) (1+ (nfix n1)))))
      ("subgoal *1/2.2" :use (:instance enum-v-next
                                        (n (nfix n1))))
      ("subgoal *1/2.1" :use (:instance enum-v-next
                                        (n (1- (nfix n2)))))))))

(acl2::with-arith5-help
 (define enum-spn
   ((p posp)
    (qmin integerp)
    (b radixp))
   :returns (spn pos-rationalp :rule-classes ())
   (* (enum-drange p b)
      (expt (radix-fix b) (ifix qmin)))
   ///
   (fty::deffixequiv enum-spn)
   (defruled enum-spn-as-expt
     (equal (enum-spn p qmin b)
            (expt (radix-fix b) (+ -1 (acl2::pos-fix p) (ifix qmin))))
     :enable enum-drange)
   (defruled enum-v-denormal-linear
     (implies (< (nfix n) (enum-drange p b))
              (< (enum-v n p qmin b) (enum-spn p qmin b)))
     :rule-classes :linear
     :enable enum-v-when-denormal)
   (defruled enum-v-enum-drange
     (equal (enum-v (enum-drange p b) p qmin b)
            (enum-spn p qmin b))
     :enable enum-v)
   (defruled enum-v-normal-linear
     (implies (<= (enum-drange p b) (nfix n))
              (<= (enum-spn p qmin b) (enum-v n p qmin b)))
     :rule-classes :linear
     :enable enum-v-enum-drange
     :use (:instance enum-v-monotone
                     (n1 (enum-drange p b))
                     (n2 n)))))

(define enum-tag
  ((c real/rationalp))
  :returns (tag natp :rule-classes ())
  (acl2::b*
   ((c (realfix c))
    (fr (mod c 1)))
   (cond ((= fr 0) 0)
         ((< fr 1/2) 1)
         ((= fr 1/2) 2)
         (t 3)))
  ///
  (fty::deffixequiv enum-tag)
  (defrule enum-tag-linear
    (and (<= 0 (enum-tag x))
         (<= (enum-tag x) 3))
    :rule-classes :linear))

(acl2::with-arith5-help
 (define enum-index
   ((x real/rationalp)
    (p posp)
    (qmin integerp)
    (b radixp))
   :returns (index natp :rule-classes () :hints (("goal" :use ret-lemma)))
   (acl2::b*
    (((unless (and (real/rationalp x) (< 0 x))) 0)
     (p (acl2::pos-fix p))
     (qmin (ifix qmin))
     (b (radix-fix b))
     (expq (expq x p b))
     (q (max qmin expq))
     (c (* x (expt b (- q))))
     (n (+ (* (- q qmin) (enum-nrange p b))
           (fl c))))
    (+ (* 4 n) (enum-tag c)))
   :prepwork
   ((local
     (acl2::with-arith5-nonlinear-help
      (defruled ret-lemma
        (acl2::b*
         ((b (radix-fix b))
          (qmin (ifix qmin))
          (p (acl2::pos-fix p))
          (expq (expq x p b))
          (q (max qmin expq))
          (c (* x (expt b (- q))))
          (n (+ (* (- q qmin) (enum-nrange p b))
                (fl c))))
         (natp (if (and (rationalp x) (< 0 x))
                   (+ (* 4 n) (enum-tag c))
                 0)))
        :prep-lemmas
        ((defrule tag-lemma-1
           (implies (<= 0 a)
                    (<= 0 (+ (enum-tag c) a))))
         (defrule tag-lemma-2
           (implies (and (<= a b)
                         (<= 0 d))
                    (<= a (+ b (enum-tag c) d)))
        ))))))
   ///
   (fty::deffixequiv enum-index)
   (defruled enum-index-denormal
     (implies (and (<= 0 (realfix x))
                   (< (realfix x) (enum-spn p qmin b)))
              (equal (enum-index x p qmin b)
                     (acl2::b*
                      ((c (* (realfix x)
                             (expt (radix-fix b) (- (ifix qmin))))))
                      (+ (* 4 (fl c)) (enum-tag c)))))
     :enable enum-spn-as-expt
     :use (:instance expq<=
                     (x (realfix x))
                     (p (acl2::pos-fix p))
                     (b (radix-fix b))
                     (n (1- (ifix qmin)))))
   (defruled enum-index-normal
     (implies (<= (enum-spn p qmin b) (realfix x))
              (equal (enum-index x p qmin b)
                     (acl2::b*
                      ((nrange (enum-nrange p b))
                       (p (acl2::pos-fix p))
                       (qmin (ifix qmin))
                       (b (radix-fix b))
                       (x (realfix x))
                       (expq (expq x p b))
                       (sigc (sigc x p b))
                       (n (+ (* (- expq qmin) nrange) (fl sigc))))
                      (+ (* 4 n) (enum-tag sigc)))))
     :enable (enum-spn-as-expt sigc sigm expq)
     :use (:instance expq>=
                     (x (realfix x))
                     (p (acl2::pos-fix p))
                     (b (radix-fix b))
                     (n (ifix qmin))))))
#|
(defruled enum-index-enum-v{n}
  (acl2::b*
   ((v{n} (enum-v n p qmin b)))
   (equal (enum-index v{n} p qmin b)
          (* 4 (nfix n))))
 :use (:instance lemma
                 (n (nfix n))
                 (p (acl2::pos-fix p))
                 (qmin (ifix qmin))
                 (b (radix-fix b)))
 :prep-lemmas
 ((acl2::with-arith5-nonlinear++-help
   (defruled lemma0
     (implies (and (<= (enum-drange p b) n)
                   (integerp n))
              (equal (* (enum-nrange p b) (enum-q n p qmin b))
                     (+ n
                        (* (ifix qmin) (enum-nrange p b))
                        (- (enum-c n p b)))))
     :enable (enum-q enum-c fl)))
  (acl2::with-arith5-nonlinear-help
   (defruled lemma
     (implies (and (natp n)
                   (posp p)
                   (integerp qmin)
                   (radixp b))
              (equal (enum-index (enum-v n p qmin b) p qmin b) (* 4 n)))
     :enable (enum-index enum-tag)
     :cases ((= n 0)
             (<= (enum-drange p b) n))
     :hints
     (("subgoal 3" :in-theory (enable enum-v-when-denormal enum-drange)
       :use (:instance expq<=
                       (x (enum-v n p qmin b))
                       (n (1- qmin))))
      ("subgoal 1" :cases
       ((not (= (expq (enum-v n p qmin b) p b) (enum-q n p qmin b)))
        (not (= (sigc (enum-v n p qmin b) p b) (enum-c n p b)))))
      ("subgoal 1.3" :in-theory (enable enum-v lemma0))
      ("subgoal 1.2" :in-theory (enable expq-enum-v-when-normal))
      ("subgoal 1.1" :in-theory (enable sigc-enum-v-when-normal)))))))
|#
(acl2::with-arith5-help
 (defruled enum-index-as-enum-v-lemma
  (acl2::b*
   ((c{n} (enum-c n p b))
    (q{n} (enum-q n p qmin b)))
   (implies (and (real/rationalp c)
                 (natp n)
                 (posp p)
                 (integerp qmin)
                 (radixp b)
                 (<= c{n} c)
                 (< c (1+ c{n})))
            (equal (enum-index (* c (expt b q{n})) p qmin b)
                   (+ (* 4 (- q{n} qmin) (enum-nrange p b))
                      (* 4 c{n})
                      (enum-tag c)))))
  :enable (enum-index-denormal
           enum-index-normal
           sigc-shift sigc-self)
  :cases ((<= (enum-drange p b) n))
  :prep-lemmas
  ((defrule lemma1
     (implies (and (< c (enum-drange p b))
                   (radixp b))
              (< (* c (expt b qmin)) (enum-spn p qmin b)))
     :enable enum-spn)
   (acl2::with-arith5-nonlinear-help
    (defrule lemma2
      (implies (and (<= (enum-drange p b) c)
                    (<= qmin q)
                    (integerp q)
                    (integerp qmin)
                    (radixp b))
               (<= (enum-spn p qmin b) (* c (expt b q))))
      :enable enum-spn))
   (defrule lemma3
     (implies (and (<= (enum-c n p b) c)
                   (< c (1+ (enum-c n p b)))
                   (<= (enum-drange p b) n)
                   (natp n)
                   (real/rationalp c)
                   (posp p)
                   (radixp b))
              (equal (sigc c p b) c))
     :enable (sigc-self enum-drange enum-nrange))
   (defrule lemma4
     (implies (and (<= (enum-c n p b) c)
                   (< c (1+ (enum-c n p b)))
                   (<= (enum-drange p b) n)
                   (natp n)
                   (real/rationalp c)
                   (posp p)
                   (radixp b))
              (equal (expq c p b) 0))
     :enable (enum-drange enum-nrange)
     :use (:instance expq-unique (x c) (n 0)))
   (defrule expq-shift-alt
     (implies (and (real/rationalp x)
                   (not (= x 0))
                   (integerp n)
                   (integerp p)
                   (radixp b))
              (equal (expq (* x (expt b n)) p b)
                     (+ n (expq x p b))))
     :use expq-shift))))
 
(acl2::with-arith5-help
 (defruled enum-index-as-enum-v-try
  (acl2::b*
   ((v{n} (enum-v n p qmin b))
    (q{n} (enum-q n p qmin b))
    (c{n} (enum-c n p b))
    (ulp (expt (radix-fix b) (enum-q n p qmin b))))
   (implies (and (natp n)
                 (posp p)
                 (integerp qmin)
                 (radixp b)
                 (real/rationalp x)
                 (<= v{n} x)
                 (< x (+ v{n} ulp)))
            (equal (enum-index x p qmin b)
                   (+ (* 4 (- q{n} qmin) (enum-nrange p b))
                      (* 4 c{n})
                      (enum-tag (* x (expt b (- q{n}))))))))
  :enable (enum-index-denormal
           enum-index-normal
           sigc-shift sigc-self
           enum-v
           )
  :cases ((<= (enum-drange p b) n))
  :prep-lemmas
  ((defruled lemma1
     (implies (and (< c (enum-drange p b))
                   (radixp b))
              (< (* c (expt b qmin)) (enum-spn p qmin b)))
     :enable enum-spn)
   (acl2::with-arith5-nonlinear-help
    (defrule lemma1a
      (implies (and (< x (+ (expt b qmin) (* n (expt b qmin))))
                    (< n (enum-drange p b))
                    (natp n)
                    (radixp b))
               (< x (enum-spn p qmin b)))
      :use (:instance lemma1 (c (* x (expt b (- qmin)))))))
   (acl2::with-arith5-nonlinear-help
    (defruled lemma2
      (implies (and (<= (enum-drange p b) c)
                    (<= qmin q)
                    (integerp q)
                    (integerp qmin)
                    (radixp b))
               (<= (enum-spn p qmin b) (* c (expt b q))))
      :enable enum-spn))
   (acl2::with-arith5-nonlinear-help
    (defrule lemma2a
      (implies (and (<= (* c (expt b q)) x)
                    (<= (enum-drange p b) c)
                    (<= qmin q)
                    (posp p)
                    (integerp q)
                    (integerp qmin)
                    (radixp b))
               (<= (enum-spn p qmin b) x))
      :use (:instance lemma2 (c (* x (expt b (- q)))))))
   (defruled lemma3
     (implies (and (<= (enum-c n p b) c)
                   (< c (1+ (enum-c n p b)))
                   (<= (enum-drange p b) n)
                   (natp n)
                   (real/rationalp c)
                   (posp p)
                   (radixp b))
              (equal (sigc c p b) c))
     :enable (sigc-self enum-drange enum-nrange))
   (acl2::with-arith5-nonlinear-help
    (defrule lemma3a
      (implies (and (<= (* (enum-c n p b) (expt b q)) x)
                    (< x (+ (expt b q) (* (enum-c n p b) (expt b q))))
                    (<= (enum-drange p b) n)
                    (natp n)
                    (real/rationalp x)
                    (integerp q)
                    (posp p)
                    (radixp b))
               (equal (sigc x p b) (* x (expt b (- q)))))
      :enable sigc-shift
      :use (:instance lemma3 (c (* x (expt b (- q)))))))
   (defruled lemma4
     (implies (and (<= (enum-c n p b) c)
                   (< c (1+ (enum-c n p b)))
                   (<= (enum-drange p b) n)
                   (natp n)
                   (real/rationalp c)
                   (posp p)
                   (radixp b))
              (equal (expq c p b) 0))
     :enable (enum-drange enum-nrange)
     :use (:instance expq-unique (x c) (n 0)))
   (defrule expq-shift-alt
     (implies (and (real/rationalp x)
                   (not (= x 0))
                   (integerp n)
                   (integerp p)
                   (radixp b))
              (equal (expq (* x (expt b n)) p b)
                     (+ n (expq x p b))))
     :use expq-shift)
   (acl2::with-arith5-nonlinear-help
    (defrule lemma4a
      (implies (and (<= (* (enum-c n p b) (expt b q)) x)
                    (< x (+ (expt b q) (* (enum-c n p b) (expt b q))))
                    (<= (enum-drange p b) n)
                    (natp n)
                    (real/rationalp x)
                    (integerp q)
                    (posp p)
                    (radixp b))
               (equal (expq x p b) q))
      :enable expq-shift-alt
      :use (:instance lemma4 (c (* x (expt b (- q)))))))
   (acl2::with-arith5-nonlinear-help
    (defrule lemma5
      (implies (and (<= (* n (expt b q)) x)
                    (< x (+ (expt b q) (* n (expt b q))))
                    (real/rationalp x)
                    (integerp q)
                    (radixp b)
                    (natp n))
               (equal (fl (* x (expt b (- q)))) n))
      :use (:instance fl-unique
                      (x (* x (expt b (- q))))))))))

(defund rne1 (sig)
  (let* ((z (fl sig))
         (f (- sig z)))
    (if (or (< f 1/2) (and (= f 1/2) (evenp z))) z (1+ z))))

(acl2::with-arith5-help
 (defruled rne1-minus
   (implies (rationalp sig)
            (equal (rne1 (- sig))
                   (- (rne1 sig))))
   :enable rne1))

(acl2::with-arith5-help
 (defruled rne-as-rne1
  (implies (and (formatp f)
                (rationalp x)
                (integerp n)
                (< 0 x))
           (equal (rne x n)
                  (let ((q (+ 1 (- n) (expo x))))
                  (* (rne1 (* x (expt 2 (- q)))) (expt 2 q)))))
 :enable (rne rtz raz sgn sig rne1)))

(acl2::with-arith5-help
 (defruled drnd-as-rne1
  (implies (and (formatp f)
                (rationalp x)
                (< 0 x))
           (equal (drnd x *RoundTiedToEven* f)
                  (let ((qmin (+ 2 (- (bias f)) (- (prec f)))))
                    (* (rne1 (* x (expt 2 (- qmin)))) (expt 2 qmin)))))
  :enable (drnd rnd rne-as-rne1 spn)))

(defruled round-f-as-rne1-x>0
  (implies (and (formatp f)
                (rationalp x)
                (< 0 x))
           (equal (round-f x f)
                  (let ((q (- (max (- 1 (bias f)) (expo x))
                              (1- (prec f)))))
                    (* (rne1 (* x (expt 2 (- q)))) (expt 2 q)))))
  :enable (round-f rnd rne-as-rne1 drnd-as-rne1)
  :use lemma
  :prep-lemmas
  ((defruled lemma
     (implies (and (formatp f)
                   (rationalp x)
                   (< 0 x))
              (equal (<= (spn f) x)
                     (<= (- 1 (bias f)) (expo x))))
     :enable (spn expo>=)
     :use (:instance expo<=
                     (n (- (bias f)))))))

(acl2::with-arith5-help
 (defruled round-f-as-rne1
  (implies (rationalp x)
           (equal (round-f x f)
                  (let* ((f (format-fix f))
                         (q (- (max (- 1 (bias f)) (expo x))
                               (1- (prec f)))))
                    (* (rne1 (* x (expt 2 (- q)))) (expt 2 q)))))
  :enable rne1-minus
  :cases ((< x 0) (= x 0) (> x 0))
  :hints (("subgoal 3" :use (:instance round-f-as-rne1-x>0
                                       (f (format-fix f))
                                       (x (- x))))
          ("subgoal 2" :in-theory (enable round-f drnd))
          ("subgoal 1" :use (:instance round-f-as-rne1-x>0
                                       (f (format-fix f)))))))

(defruled round-f-as-rne1-aaa
  (implies (pos-rationalp x)
           (equal (round-f x f)
                  (* (rne1 (c x f)) (expt 2 (q x f)))))
  :enable (round-f-as-rne1 c q-as-expe)
  :prep-lemmas
  ((defrule expo-as-expe
     (equal (expe x 2)
            (expo x))
     :enable (expe expo))))

(rule
 (implies (rationalp x)
          (equal (in-tau-intervalp x (Rv v f))
                 (acl2::b*
                  ((c (c v f))
                   (q (q v f))
                   (regular (or (not (= c (2^{P-1} f))) (= q (Qmin f))))
                   (vl (* (- c (if regular 1/2 1/4)) (expt 2 q)))
                   (vr (* (+ c 1/2) (expt 2 q))))
                 (if (integerp (/ c 2))
                     (and (<= vl x) (<= x vr))
                   (and (< vl x) (< x vr))))))
 :enable (in-tau-intervalp-Rv vl-alt vr))

(acl2::with-arith5-nonlinear-help
 (defruled Rv-lemma-1
  (acl2::b*
   ((q (Qmin f))
    (ulp (expt 2 q))
    (v (* c ulp)))
   (implies (and (posp c)
                 (< c (* 2 (2^{P-1} f)))
                 (pos-rationalp x)
                 (if (integerp (* 1/2 c))
                     (and (<= (- v (/ ulp 2)) x)
                          (<= x (+ v (/ ulp 2))))
                   (and (< (- v (/ ulp 2)) x)
                        (< x (+ v (/ ulp 2))))))
            (equal (round-f x f) v)))
  :enable (round-f-as-rne1-aaa rne1)
  :cases ((= (q x f) (Qmin f)))
  :hints
  (("subgoal 2" :in-theory (enable q 2^{P-1}) :use
    (:instance expq<=
               (b 2)
               (n (Qmin f))
               (p (P f))))
   ("subgoal 1" :cases ((<= (* c (expt 2 (Qmin f))) x)))
   ("subgoal 1.2" :in-theory (enable c) :cases ((equal (fl (c x f)) (1- c))))
   ("subgoal 1.2.2" :in-theory (enable c)
    :use (:instance fl-unique (x (c v f)) (n (1- c))))
   ("subgoal 1.1" :in-theory (enable c) :cases ((equal (fl (c x f)) c)))
   ("subgoal 1.1.2" :use (:instance fl-unique (x (c v f)) (n c))))))

(acl2::with-arith5-nonlinear-help
 (defruled Rv-lemma-2
  (acl2::b*
   ((c (2^{P-1} f))
    (ulp (expt 2 q))
    (v (* c ulp)))
   (implies (and (integerp q)
                 (<= (1+ (Qmin f)) q)
                 (pos-rationalp x)
                 (<= (- v (/ ulp 4)) x)
                 (<= x (+ v (/ ulp 2))))
            (equal (round-f x f) v)))
  :enable (round-f-as-rne1-aaa rne1)
  :cases ((<= (* (2^{P-1} f) (expt 2 q)) x))
  :hints
  (("subgoal 2" :cases ((< (q x f) (1- q))
                        (> (q x f) (1- q))
                        (= (q x f) (1- q))))
   ("subgoal 2.3" :in-theory (enable q 2^{P-1}) :use
    (:instance expq>=
               (b 2)
               (n (1- q))
               (p (P f))))
   ("subgoal 2.2" :in-theory (enable q 2^{P-1}) :use
    (:instance expq<=
               (b 2)
               (n (1- q))
               (p (P f))))
   ("subgoal 2.1" :in-theory (enable c)
    :cases ((equal (fl (c x f)) (1- (* 2 (2^{P-1} f))))))
   ("subgoal 1" :cases ((< (q x f) q)
                        (> (q x f) q)
                        (= (q x f) q)))
   ("subgoal 1.3" :in-theory (enable q 2^{P-1}) :use
    (:instance expq>=
               (b 2)
               (n q)
               (p (P f))))
   ("subgoal 1.2" :in-theory (enable q 2^{P-1}) :use
    (:instance expq<=
               (b 2)
               (n q)
               (p (P f))))
   ("subgoal 1.1" :in-theory (enable c)
    :cases ((equal (fl (c x f)) (2^{P-1} f))))
   ("subgoal 1.1.1.3" :in-theory (enable 2^{P-1})))))

(acl2::with-arith5-nonlinear-help
 (defruled Rv-lemma-3
  (acl2::b*
   ((ulp (expt 2 q))
    (v (* c ulp)))
   (implies (and (integerp q)
                 (<= (1+ (Qmin f)) q)
                 (integerp c)
                 (<= (1+ (2^{P-1} f)) c)
                 (<= c (1- (* 2 (2^{P-1} f))))
                 (pos-rationalp x)
                 (if (integerp (* 1/2 c))
                     (and (<= (- v (/ ulp 2)) x)
                          (<= x (+ v (/ ulp 2))))
                   (and (< (- v (/ ulp 2)) x)
                        (< x (+ v (/ ulp 2))))))
            (equal (round-f x f) v)))
  :enable (round-f-as-rne1-aaa rne1)
  :cases ((= (q x f) q))
  :hints
  (("subgoal 2" :in-theory (enable q 2^{P-1})
    :cases ((< (q x f) q) (> (q x f) q)))
   ("subgoal 2.2" :use
    (:instance expq>=
               (b 2)
               (n q)
               (p (P f))))
   ("subgoal 2.1" :use
    (:instance expq<=
               (b 2)
               (n q)
               (p (P f))))
   ("subgoal 1" :cases ((<= (* c (expt 2 q)) x)))
   ("subgoal 1.2" :in-theory (enable c) :cases ((equal (fl (c x f)) (1- c))))
   ("subgoal 1.1" :in-theory (enable c) :cases ((equal (fl (c x f)) c))))))

(acl2::with-arith5-nonlinear-help
 (defruled Rv-lemma
  (implies (and (pos-rationalp x)
                (in-tau-intervalp x (Rv v f))
                (integerp (c v f)))
           (equal (round-f x f) (pos-rational-fix v)))
  :enable (in-tau-intervalp-Rv
           vl-alt vr)
  :cases ((= (q v f) (Qmin f))
          (>= (q v f) (1+ (Qmin f))))
  :hints
  (("subgoal 2" :cases ((= (pos-rational-fix v)
                           (* (c v f) (expt 2 (q v f)))))
    :use (:instance Rv-lemma-1 (c (c v f))))
   ("subgoal 2.2" :in-theory (enable c))
   ("subgoal 1" :cases ((= (c v f) (2^{P-1} f))
                        (>= (c v f) (1+ (2^{P-1} f)))))
   ("subgoal 1.3"
    :use (:instance c-as-sigc (x (pos-rational-fix v)))
    :cases ((<= (2^{P-1} f) (sigc (pos-rational-fix v) (P f) 2))))
   ("subgoal 1.3.2" :in-theory (enable sigc-lower-bound 2^{P-1}))
   ("subgoal 1.3.1" :in-theory (enable q))
   ("subgoal 1.2" :cases ((= (pos-rational-fix v)
                             (* (c v f) (expt 2 (q v f)))))
    :use (:instance Rv-lemma-2 (q (q v f))))
   ("subgoal 1.2.2" :in-theory (enable c))
   ("subgoal 1.1" :cases ((= (pos-rational-fix v)
                             (* (c v f) (expt 2 (q v f)))))
    :use (:instance Rv-lemma-3
                    (c (c v f))
                    (q (q v f))))
   ("subgoal 1.1.2" :in-theory (enable c)))))

(acl2::with-arith5-help
 (rule
  (implies (and (in-tau-intervalp x (Rv v f))
                (finite-positive-binary-p v f)
                (pos-rationalp x))
           (equal (round-f x f) (pos-rational-fix v)))
  :enable Rv-lemma
  :use (:instance finite-positive-binary-necc (x v))))

#|
(acl2::with-arith5-nonlinear-help
 (rule
 (acl2::b*
  ((q (Qmin f)))
  (implies (and (rationalp c)
                (< 1/2 c)
                (< c (- (2^{P-1} f) 1/2)))
           (equal (q (* (rne1 c) (expt 2 q)) f)
                  q)))
 :enable (rne1 q pos-rational-fix)
 :cases ((<
 ))

(acl2::with-arith5-nonlinear-help
 (rule
  (acl2::b*
   ((v (round-f x f)))
   (implies (and (rationalp x)
                 (< (* 1/2 (expt 2 (Qmin f))) x)
                 (< x (expt 2 (Qmin f))))
            (in-tau-intervalp x (Rv v f))))
  :enable (round-f-as-rne1-aaa
           in-tau-intervalp-Rv vl-alt vr rne1)
  :prep-lemmas
  ((acl2::with-arith5-nonlinear-help
    (defrule lemma1
     (implies (and (rationalp x)
                 (< 0 x)
                 (< x (* 2 (2^{P-1} f) (expt 2 (Qmin f)))))
              (equal (q x f) (Qmin f)))
     :enable (q 2^{P-1})
     :use (:instance expq<=
                     (b 2)
                     (n (Qmin f))
                     (p (P f)))
     )))
  ))

(acl2::with-arith5-nonlinear-help
 (rule
 (implies (and (finite-positive-binary-p v f)
               (real/rationalp x)
               (in-tau-intervalp x (Rv v f)))
          (equal (round-f x f) v))
 :enable (in-tau-intervalp-Rv
          round-f-as-rne1-aaa
          vl-alt vr
          c rne1
                              ;pos-rationalp
                              )
 :use (;round-f-as-rne1-aaa
       (:instance finite-positive-binary-necc (x v)))
 ))
|#
