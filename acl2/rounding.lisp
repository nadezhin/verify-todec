(in-package "RTL")
(include-book "section5")

(local (include-book "rtl/rel11/support/round" :dir :system))
(local (acl2::allow-arith5-help))


; enumerate nonnegative values of format f

(defruled expo-as-expe
  (equal (expo x)
         (expe x 2))
  :enable (expo expe))

(acl2::with-arith5-help
 (defruled sigc-as-expq
   (implies (and (real/rationalp x)
                 (not (= x 0))
                 (integerp p)
                 (radixp b))
            (equal (sigc x p b)
                   (* (abs x) (expt b (- (expq x p b))))))
   :enable (sigc expq sigm)))

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
 (define enumerate
   ((n integerp)
    (p posp)
    (b radixp))
   :returns (v integerp :rule-classes :type-prescription)
   (acl2::b*
    ((p (acl2::pos-fix p))
     (b (radix-fix b)))
    (if (zip n)
        0
      (if (<= 0 n)
          (let ((x (enumerate (1- n) p b)))
            (+ x (max 1 (expt b (expq x p b)))))
        (let ((x (enumerate (1+ n) p b)))
          (- x (max 1 (expt b (expq x p b))))))))
   ///
   (fty::deffixequiv enumerate)
   (defrule enumerate-0
     (equal (enumerate 0 p b) 0))
   (defruled enumerate-minus
     (equal (enumerate (- n) p b)
            (- (enumerate n p b)))
     :disable expq-minus
     :induct (enumerate n p b)
     :hints
     (("subgoal *1/3" :use (:instance expq-minus
                                      (x (enumerate (1+ n) p b))
                                      (p (acl2::pos-fix p))
                                      (b (radix-fix b))))
      ("subgoal *1/2" :use (:instance expq-minus
                                      (x (enumerate (1- n) p b))
                                      (p (acl2::pos-fix p))
                                      (b (radix-fix b))))))
   (defruled signum-enumerate
     (equal (signum (enumerate n p b))
            (signum (ifix n)))
     :enable signum)))

(defrule enumerate-pos-type
  (implies (posp n)
           (posp (enumerate n p b)))
  :rule-classes :type-prescription
  :enable signum
  :use signum-enumerate)

(defrule enumerate-neg-type
  (implies (and (integerp n)
                (< n 0))
           (and (integerp (enumerate n p b))
                (< (enumerate n p b) 0)))
  :rule-classes :type-prescription
  :enable signum
  :use signum-enumerate)

(defruled enumerate-monotone
  (implies (< (ifix n1) (ifix n2))
           (< (enumerate n1 p b) (enumerate n2 p b)))
  :enable enumerate-minus
  :cases ((<= (ifix n2) 0) (<= 0 (ifix n1)))
  :hints
  (("subgoal 2" :use (:instance lemma
                                (n1 (- (ifix n2)))
                                (n2 (- (ifix n1)))
                                (b (radix-fix b))))
   ("subgoal 1" :use (:instance lemma
                                (n1 (ifix n1))
                                (n2 (ifix n2))
                                (b (radix-fix b)))))
  :prep-lemmas
  ((defrule lemma
     (implies (and (natp n1)
                   (integerp n2)
                   (< n1 n2)
                   (radixp b))
              (< (enumerate n1 p b) (enumerate n2 p b)))
     :enable enumerate
     :induct (enumerate n2 p b))))

(defruled enumerate-when-abs{n}<=drange+nrange
  (implies (<= (abs (ifix n))
               (+ (enum-drange p b) (enum-nrange p b)))
            (equal (enumerate n p b) (ifix n)))
   :enable enumerate
   :induct (enumerate n p b)
   :hints (("subgoal *1/3" :use (:instance lemma
                                           (n (1+ (ifix n)))
                                           (p (acl2::pos-fix p))
                                           (b (radix-fix b)))))
   :prep-lemmas
   ((acl2::with-arith5-help
     (defrule lemma
      (implies (and (< (abs n) (+ (enum-drange p b) (enum-nrange p b)))
                    (posp p)
                    (radixp b))
               (<= (expt b (expq n p b)) 1))
      :rule-classes :linear
      :enable (enum-drange enum-nrange)
      :use (:instance expq<= (x (abs (realfix n))) (n 0))
      :cases ((= (realfix n) 0))
      :hints (("subgoal 1" :in-theory (enable expq expe)))))))

(defruled expq-enumerate-normal-type
  (implies (and (or (<= n (- (enum-drange p b)))
                    (<= (enum-drange p b) n))
                (integerp n)
                (posp p)
                (radixp b))
           (and (integerp (expq (enumerate n p b) p b))
                (<= 0 (expq (enumerate n p b) p b))))
  :enable enumerate-minus
  :use (:instance lemma (n (- n)))
  :rule-classes :type-prescription
  :prep-lemmas
  ((acl2::with-arith5-help
    (defrule lemma
      (implies (and (<= (enum-drange p b) n)
                    (integerp n)
                    (posp p)
                    (radixp b))
               (and (integerp (expq (enumerate n p b) p b))
                    (<= 0 (expq (enumerate n p b) p b))))
      :enable (enumerate-when-abs{n}<=drange+nrange enum-drange)
      :use ((:instance expq>=
                       (x (enumerate n p b))
                       (n 0))
            (:instance enumerate-monotone
                       (n1 (enum-drange p b))
                       (n2 (abs n))))))))

(defruled enumerate-normal-as-fpr+
  (implies (and (<= (enum-drange p b) n)
                (integerp n))
           (equal (enumerate (1+ n) p b)
                  (fpr+ (enumerate n p b)
                        (acl2::pos-fix p)
                        (radix-fix b))))
  :use (:instance lemma
                  (p (acl2::pos-fix p))
                  (b (radix-fix b)))
  :prep-lemmas
  ((acl2::with-arith5-help
    (defrule lemma
      (implies (and (<= (enum-drange p b) n)
                    (integerp n)
                    (posp p)
                    (radixp b))
               (equal (enumerate (1+ n) p b)
                      (fpr+ (enumerate n p b) p b)))
      :enable (expq-enumerate-normal-type enumerate)))))

(defrule exactrp-enumerate
  (implies (and (posp p)
                (radixp b))
           (exactrp (enumerate n p b) p b))
  :enable enumerate-minus
  :cases ((zip n))
  :hints
  (("subgoal 2" :use (:instance lemma (n (- n))))
   ("subgoal 1" :in-theory (enable enumerate)))
  :prep-lemmas
  ((acl2::with-arith5-nonlinear-help
    (defrule lemma
     (implies (and (natp n)
                   (posp p)
                   (radixp b))
              (exactrp (enumerate n p b) p b))
     :induct (sub1-induction n)
     :hints
     (("subgoal *1/2" :cases ((<= (1+ (enum-drange p b)) n)))
      ("subgoal *1/2.2" :use (:instance dvecp-exactrp
                                        (x n))
       :in-theory (enable enumerate-when-abs{n}<=drange+nrange
                          dvecp enum-drange))
      ("subgoal *1/2.1" :cases ((posp (1- n)))
       :in-theory (enable enumerate-pos-type)
       :use
       ((:instance enumerate-normal-as-fpr+
                   (n (1- n)))
        (:instance fpr+1
                   (x (enumerate (1- n) p b)))))
      ("subgoal *1/1" :in-theory (enable enumerate)))))))

(defruled enumerate-normal-as-fpr-
  (implies (and (< (enum-drange p b) n)
                (integerp n))
           (equal (enumerate (1- n) p b)
                  (fpr- (enumerate n p b)
                        (acl2::pos-fix p)
                        (radix-fix b))))
  :enable enumerate-normal-as-fpr+
  :disable (fpr+ fpr- fpr-+)
  :cases ((posp (1- n)))
  :use ((:instance fpr-+
                   (x (enumerate (1- n) p b))
                   (p (acl2::pos-fix p))
                   (b (radix-fix b)))
        (:instance enumerate-normal-as-fpr+
                   (n (1- n)))
        (:instance exactrp-enumerate
                   (n (1- n))
                   (p (acl2::pos-fix p))
                   (b (radix-fix b)))))

(acl2::with-arith5-nonlinear-help
 (defruled expq-sigc-enumerate-n+1
  (acl2::b*
   ((drange (enum-drange p b))
    (nrange (enum-nrange p b))
    (v (enumerate n p b))
    (v+ (enumerate (1+ n) p b)))
   (implies (and (<= drange n)
                 (integerp n)
                 (posp p)
                 (radixp b))
            (and (equal (expq v+ p b)
                        (if (= (sigc v p b) (+ -1 drange nrange))
                            (1+ (expq v p b))
                          (expq v p b)))
                 (equal (sigc v+ p b)
                        (if (= (sigc v p b) (+ -1 drange nrange))
                            drange
                          (1+ (sigc v p b)))))))
   :enable (enumerate-normal-as-fpr+ sigc-as-expq)
   :cases ((= (expq (enumerate (1+ n) p b) p b)
              (expq (enumerate n p b) p b))
           (= (enumerate (1+ n) p b)
              (expt b (+ p (expq (enumerate n p b) p b)))))
   :hints
   (("subgoal 3" :use (:instance fpr+expq
                                 (x (enumerate n p b))))
    ("subgoal 1" :in-theory (enable enum-drange enum-nrange)))
   :prep-lemmas
   ((defrule lemma
      (implies (and (equal (1+ (sigc x p b))
                           (+ (enum-drange p b) (enum-nrange p b)))
                    (real/rationalp x)
                    (< 0 x)
                    (posp p)
                    (radixp b))
               (equal (expq (+ x (expt b (expq x p b))) p b)
                      (1+ (expq x p b))))
      :enable (enum-nrange enum-drange sigc-as-expq)
      :use (:instance expq-shift
                      (x (1+ (sigc x p b)))
                      (n (expq x p b)))))))

(acl2::with-arith5-nonlinear-help
 (defruled expq-sigc-enumerate
  (acl2::b*
   ((drange (enum-drange p b))
    (nrange (enum-nrange p b))
    (v (enumerate n p b))
    (q (fl (/ (- n drange) nrange))))
   (implies (and (<= drange n)
                 (integerp n)
                 (posp p)
                 (radixp b))
            (and (equal (expq v p b) q)
                 (equal (sigc v p b) (- n (* q nrange))))))
  :induct (sub1-induction n)
  :hints
  (("subgoal *1/2" :cases ((= n (enum-drange p b))
                           (>= n (1+ (enum-drange p b)))))
   ("subgoal *1/2.2" :in-theory
    (enable enumerate-when-abs{n}<=drange+nrange enum-drange sigc-as-expq))
   ("subgoal *1/2.1" :cases ((= (sigc (enumerate (1- n) p b) p b)
                                (+ -1 (enum-drange p b) (enum-nrange p b))))
    :use (:instance expq-sigc-enumerate-n+1
                    (n (1- n))))
   ("subgoal *1/2.1.2" :use
    (:instance lemma
               (n (- (1- n) (enum-drange p b)))
               (m (enum-nrange p b)))))
  :prep-lemmas
  ((defruled lemma
     (implies (and (posp m)
                   (integerp n)
                   (not (= (- n (* m (fl (/ n m)))) (1- m))))
              (equal (fl (/ (1+ n) m)) (fl (/ n m))))))))

(defruled enumerate-explicit
  (acl2::b*
   ((drange (enum-drange p b))
    (nrange (enum-nrange p b))
    (an (abs (ifix n)))
    (q (fl (/ (- an drange) nrange)))
    (c (- an (* q nrange)))
    (v (* c (expt (radix-fix b) q))))
   (equal (enumerate n p b)
          (if (< an drange)
              (ifix n)
            (if (<= 0 (ifix n)) v (- v)))))
  :disable ifix
  :use (:instance lemma
                  (n (ifix n))
                  (p (acl2::pos-fix p))
                  (b (radix-fix b)))
  :prep-lemmas
  ((acl2::with-arith5-help
    (defruled lemma
      (acl2::b*
       ((drange (enum-drange p b))
        (nrange (enum-nrange p b))
        (an (abs n))
        (q (fl (/ (- an drange) nrange)))
        (c (- an (* q nrange)))
        (v (* c (expt b q))))
       (implies (and (integerp n)
                     (posp p)
                     (radixp b))
                (equal (enumerate n p b)
                       (if (< an drange)
                           n
                         (if (<= 0 n) v (- v))))))
      :enable (enumerate-minus sigc-as-expq)
      :cases ((<= n (- (enum-drange p b)))
              (<= (enum-drange p b) n))
      :hints
      (("subgoal 3" :in-theory (enable enumerate-when-abs{n}<=drange+nrange))
       ("subgoal 2" :use (:instance expq-sigc-enumerate (n (- n))))
       ("subgoal 1" :use (:instance expq-sigc-enumerate)))
      :prep-lemmas
      ((acl2::with-arith5-nonlinear++-help
        (defrule lemma0
          (implies (and (equal (+ n (* nrange expq)) (* v (expt b (- q))))
                        (real/rationalp v)
                        (radixp b))
                   (equal (+ (* n (expt b q)) (* nrange expq (expt b q)))
                          v)))))))))

(acl2::with-arith5-nonlinear-help
 (defruled enumerate-explicit-corr
   (acl2::b*
    ((drange (enum-drange p b))
     (nrange (enum-nrange p b))
     (n (+ c (* q nrange))))
    (implies (and (natp q)
                  (integerp c)
                  (<= drange c)
                  (< c (+ drange nrange)))
             (equal (enumerate n p b)
                    (* c (expt (radix-fix b) q)))))
   :use ((:instance enumerate-explicit
                    (n (+ c (* q (enum-nrange p b)))))
         (:instance fl-unique
                    (x (/ (- (+ c (* q (enum-nrange p b)))
                             (enum-drange p b))
                          (enum-nrange p b)))
                    (n q)))))

(acl2::with-arith5-help
 (defrule expq-enumerate-upper-bound
   (implies (and (< (abs n) (+ (enum-drange p b)
                               (* q (enum-nrange p b))))
                 (not (zip n))
                 (natp q)
                 (posp p)
                 (radixp b))
            (< (expq (enumerate n p b) p b) q))
   :enable (enumerate-minus enum-drange)
   :use ((:instance expq<=
                    (x (enumerate (abs n) p b))
                    (n (1- q)))
         (:instance enumerate-monotone
                    (n1 (abs n))
                    (n2 (+ (enum-drange p b)
                           (* q (enum-nrange p b)))))
         (:instance enumerate-explicit-corr
                    (c (enum-drange p b))))))

(define enumerate-f
  ((n integerp)
   (f formatp))
  :returns (v rationalp :rule-classes ())
  (acl2::b*
   ((f (format-fix f)))
   (* (spd f) (enumerate n (prec f) 2)))
  ///
  (fty::deffixequiv enumerate-f :hints (("goal" :in-theory (disable ifix))))
  (defrule enumerate-f-0
    (equal (enumerate-f 0 f) 0))
  (acl2::with-arith5-help
   (defruled enumerate-f-minus
     (equal (enumerate-f (- n) f)
            (- (enumerate-f (fix n) f)))
     :enable enumerate-minus))
  (defruled signum-enumerate-f
    (equal (signum (enumerate-f n f))
           (signum (ifix n)))
    :enable signum
    :use (:instance signum-enumerate
                    (p (prec (format-fix f)))
                    (b 2)))
  (defrule enumerate-f-pos-type
    (implies (posp n)
             (pos-rationalp (enumerate-f n f)))
    :rule-classes :type-prescription)
  (acl2::with-arith5-help
  (defrule enumerate-f-neg-type
    (implies (and (integerp n)
                  (< n 0))
             (and (rationalp (enumerate-f n f))
                  (< (enumerate-f n f) 0)))
    :rule-classes :type-prescription)
  (defruled enumerate-f-monotone
    (implies (< (ifix n1) (ifix n2))
             (< (enumerate-f n1 f) (enumerate-f n2 f)))
    :enable enumerate-monotone)
  (defruled enumerate-f-when-abs{n}<=drange+nrange
    (implies (<= (abs (ifix n)) (expt 2 (prec (format-fix f))))
             (equal (enumerate-f n f)
                    (* (spd (format-fix f)) (ifix n))))
    :enable (enum-drange enum-nrange acl2::pos-fix)
    :use (:instance enumerate-when-abs{n}<=drange+nrange
                    (b 2)
                    (p (prec (format-fix f)))));)
  (defruled expo-enumerate-f
    (equal (expo (enumerate-f n f))
           (if (zip n)
               0
             (let ((f (format-fix f)))
               (- (expq (enumerate n (prec f) 2) (prec f) 2)
                  (1- (bias f))))))
    :enable (spd expq expo-as-expe)
    :use (:instance expe-shift
                    (b 2)
                    (x (enumerate n (prec (format-fix f)) 2))
                    (n (+ 2 (- (bias (format-fix f))) (- (prec (format-fix f))))))
    :cases ((zip n) (posp n))
    :hints (("subgoal 2" :in-theory (enable enumerate)))
    :prep-lemmas
    ((defrule lemma
       (implies (formatp f)
                (integerp (+ (bias f) (prec f)))))))))


(acl2::with-arith5-nonlinear-help
 (rule
  (implies (and (not (zip n))
                (< (abs n) (expt 2 (1- (prec f))))
                (formatp f))
           (drepp (enumerate-f n f) f))
  :enable (enumerate-f enumerate-when-abs{n}<=drange+nrange
           drepp spd exactp sig enum-drange)
  :use ((:instance expo>=
                   (x (* (enumerate (abs n) (prec f) 2) (spd f)))
                   (n (expo (spd f))))
        (:instance expo<=
                   (x (* (enumerate (abs n) (prec f) 2) (spd f)))
                   (n (- (bias f)))))))
#|
(acl2::with-arith5-nonlinear-help
 (rule
  (implies (and (<= (expt 2 (1- (prec f))) (abs n))
                (< (abs n) (* (1- (expt 2 (expw f)))
                              (expt 2 (1- (prec f)))))
                (posp n)
                (formatp f))
           (nrepp (enumerate-f n f) f))
  :enable (nrepp;enumerate-when-abs{n}<=drange+nrange
;           enum-drange
           enumerate-minus
           ;spd
           ;spn exactp sig
           )
  :cases
  ((not (<= (- 1 (bias f))
            (expo (enumerate-f n f))))
   (not (<= (expo (enumerate-f n f))
            (+ -2 (- (bias f)) (expt 2 (expw f)))))
   (not (exactp (enumerate-f n f) (prec f))))
  :prep-lemmas
  ((defrule expo-spd
     (implies (and (posp x)
                   (formatp f))
              (equal (expo (* (spd f) x))
                     (+ 1 (expq x (prec f) 2) (- (bias f)))))
     :enable (spd expq expo-as-expe)
     :use (:instance expe-shift
                     (b 2)
                     (n (+ 2 (- (bias f)) (- (prec f)))))
     )
  )))
  :hints
  (("subgoal 3"
    :in-theory (enable enumerate-when-abs{n}<=drange+nrange enum-drange)
    :use
    ((:instance expo>=
                (x (* (enumerate (abs n) (prec f) 2) (spd f)))
                (n (- 1 (bias f))))
     (:instance enumerate-monotone
                (n1 (expt 2 (1- (prec f))))
                (n2 (abs n))
                (p (prec f))
                (b 2))))
   ("subgoal 2" :use (:instance expq-enumerate-upper-bound
                                (q (
   ("subgoal 2" :cases ((< (* (enumerate (abs n) (prec f) 2) (spd f))
                           (expt 2 (+ -2 (- (bias f)) (expt 2 (expw f)))))))
   ("subgoal 2.2" :cases ((not (= (enumerate
                              (* (1- (expt 2 (expw f)))
                                 (expt 2 (1- (prec f))))
                              (prec f)
                              2)
                             (expt 2 (+ -2 (- (bias f))
                                        (expt 2 (expw f)))))))

    :use (:instance enumerate-monotone
                    (n1 (abs n))
                    (n2 (* (1- (expt 2 (expw f)))
                           (expt 2 (1- (prec f)))))))
   ("subgoal 2.1" :use
    ((:instance expo<=
                (x (* (enumerate (abs n) (prec f) 2) (spd f)))
                (n (+ -2 (- (bias f)) (expt 2 (expw f)))))
     )
    )))

   )))))
  :use ((:instance expo>=
                   (x (* (enumerate (abs n) (prec f) 2) (spd f)))
                   (n (expo (spn f))))
        (:instance enumerate-monotone
                   (n1 (expt 2 (1- (prec f))))
                   (n2 (abs n))
                   (p (prec f))
                   (b 2)))
        ;(:instance expo<=
         ;          (x (* (enumerate (abs n) (prec f) 2) (spd f)))
         ;          (n (1- (expo (spn f)))))
        )))
|#
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

(rule
 (equal (enum-q n p qmin b)
        (+ (ifix qmin)
           (if (< (nfix n) (enum-drange p b))
               0
             (expq (enumerate (nfix n) p b)
                   (acl2::pos-fix p)
                   (radix-fix b)))))
 :enable (enumerate-when-abs{n}<=drange+nrange enum-q)
 :use (:instance expq-sigc-enumerate
                  (n (ifix n))
                  (p (acl2::pos-fix p))
                  (b (radix-fix b))))

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

(rule
 (equal (enum-c n p b)
        (if (< (nfix n) (enum-drange p b))
            (nfix n)
          (sigc (enumerate (nfix n) p b)
                (acl2::pos-fix p)
                (radix-fix b))))
 :enable enum-c
 :use ((:instance expq-sigc-enumerate
                  (n (ifix n))
                  (p (acl2::pos-fix p))
                  (b (radix-fix b)))
       (:instance mod-def
                  (x (- n (enum-drange p b)))
                  (y (enum-nrange p b)))))

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
 (rule
  (equal (enum-v n p qmin b)
         (* (enumerate (nfix n) p b)
            (expt (radix-fix b) (ifix qmin))))
  :enable (enumerate-explicit enum-v enum-c enum-q)
  :use (:instance mod-def
                  (x (- n (enum-drange p b)))
                  (y (enum-nrange p b)))))


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
#|
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
|#
(acl2::with-arith5-help
 (define enum-index-aux
   ((x real/rationalp)
    (p posp)
    (qmin integerp)
    (b radixp)
    (n natp))
   :measure (nfix (1+ (fl (/ (- (realfix x) (enum-v (1+ (nfix n)) p qmin b))
                             (expt (radix-fix b) qmin)))))
   :returns (n natp :rule-classes ())
   (let ((n (nfix n)))
     (if (< (realfix x) (enum-v (1+ n) p qmin b))
         n
       (enum-index-aux x p qmin b (1+ n))))
   :hints
   (("goal" :use
     ((:instance enum-v-next
                 (n (1+ (nfix n))))
      (:instance n<=fl-linear
                 (x (/ (- (realfix x) (enum-v (1+ (nfix n)) p qmin b))
                       (expt (radix-fix b) qmin)))
                 (n 0)))))
   ///
   (fty::deffixequiv enum-index-aux
                     :hints (("goal" :in-theory (disable ifix))))
   (defrule enum-index-aux-def
     (implies (<= (enum-v n p qmin b) (realfix x))
              (let ((index (enum-index-aux x p qmin b n)))
                (and (<= (enum-v index p qmin b) (realfix x))
                     (< (realfix x) (enum-v (1+ index) p qmin b)))))
     :rule-classes ())
   (defruled enum-index-aux-lower-bound
     (<= (nfix n) (enum-index-aux x p qmin b n))
     :rule-classes :linear)
   (defrule enum-index-aux-monotone
     (implies (<= (realfix x1) (realfix x2))
              (<= (enum-index-aux x1 p qmin b n)
                  (enum-index-aux x2 p qmin b n)))
     :rule-classes ()
     :induct (enum-index-aux x1 p qmin b n)
     :enable enum-index-aux-lower-bound)))

(define enum-index
   ((x real/rationalp)
    (p posp)
    (qmin integerp)
    (b radixp))
   :returns (index natp :rule-classes ())
   (enum-index-aux x p qmin b 0)
   ///
   (fty::deffixequiv enum-index)
   (defrule enum-index-def
     (implies (<= 0 (realfix x))
              (let ((index (enum-index x p qmin b)))
                (and (<= (enum-v index p qmin b) (realfix x))
                     (< (realfix x) (enum-v (1+ index) p qmin b)))))
     :rule-classes ()
     :use (:instance enum-index-aux-def (n 0)))
   (defrule enum-index-monotone
     (implies (<= (realfix x1) (realfix x2))
              (<= (enum-index x1 p qmin b)
                  (enum-index x2 p qmin b)))
     :rule-classes ()
     :use (:instance enum-index-aux-monotone (n 0))))

(acl2::with-arith5-help
 (define enum-index-old
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
     (c (* x (expt b (- q)))))
    (+ (* (- q qmin) (enum-nrange p b))
       (fl c)))
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
          (c (* x (expt b (- q)))))
         (natp (if (and (rationalp x) (< 0 x))
                   (+ (* (- q qmin) (enum-nrange p b))
                      (fl c))
                 0)))))))
   ///
   (fty::deffixequiv enum-index-old)
   (defruled enum-index-old-denormal
     (implies (and (<= 0 (realfix x))
                   (< (realfix x) (enum-spn p qmin b)))
              (equal (enum-index-old x p qmin b)
                     (fl (* (realfix x)
                            (expt (radix-fix b) (- (ifix qmin)))))))
     :enable enum-spn-as-expt
     :use (:instance expq<=
                     (x (realfix x))
                     (p (acl2::pos-fix p))
                     (b (radix-fix b))
                     (n (1- (ifix qmin)))))
   (defruled enum-index-old-normal
     (implies (<= (enum-spn p qmin b) (realfix x))
              (equal (enum-index-old x p qmin b)
                     (acl2::b*
                      ((nrange (enum-nrange p b))
                       (p (acl2::pos-fix p))
                       (qmin (ifix qmin))
                       (b (radix-fix b))
                       (x (realfix x))
                       (expq (expq x p b))
                       (sigc (sigc x p b)))
                      (+ (* (- expq qmin) nrange) (fl sigc)))))
     :enable (enum-spn-as-expt sigc sigm expq)
     :use (:instance expq>=
                     (x (realfix x))
                     (p (acl2::pos-fix p))
                     (b (radix-fix b))
                     (n (ifix qmin))))))
#|
(acl2::with-arith5-help
 (defruled enum-index-old-as-enum-v-lemma
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
            (equal (enum-index-old (* c (expt b q{n})) p qmin b)
                   (+ (* (- q{n} qmin) (enum-nrange p b))
                      c{n}))))
  :enable (enum-index-old-denormal
           enum-index-old-normal
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
|#
(acl2::with-arith5-help
 (defruled enum-index-old-as-enum-v
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
            (equal (enum-index-old x p qmin b)
                   (+ (* (- q{n} qmin) (enum-nrange p b))
                      c{n}))))
  :enable (enum-index-old-denormal
           enum-index-old-normal
           sigc-shift sigc-self
           enum-v)
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

(acl2::with-arith5-help
 (defruled drepp-enum-v
  (implies (and (formatp f)
                (posp n)
                (< n (enum-drange (P f) 2)))
           (drepp (enum-v n (P f) (Qmin f) 2) f))
  :enable (enum-v-when-denormal
           enum-drange drepp Qmin P 2^{W-1}-as-bias exactp2)
  :use ((:instance expo-shift
                  (x n)
                  (n (Qmin f)))
        (:instance expo>=
                   (x n)
                   (n 0))
        (:instance expo<=
                   (x n)
                   (n (- (P f) 2))))))

(acl2::with-arith5-help
 (defrule exactp-enum-v
   (exactp (enum-v n (P f) (Qmin f) 2) (P f))
   :enable (enum-v-when-denormal)
   :cases ((zp n)
           (<= (enum-drange (P f) 2) (nfix n)))
   :hints
   (("subgoal 3" :cases ((<= (expo (* n (expt 2 (Qmin f))))
                             (+ -1 (P f) (Qmin f)))))
    ("subgoal 3.2" :in-theory (enable enum-drange)
     :use (:instance expo<=
                     (x (* n (Expt 2 (Qmin f))))
                     (n (+ -2 (P f) (Qmin f)))))
    ("subgoal 3.1" :in-theory (enable exactp2))
    ("subgoal 2" :in-theory (enable exactp2))
    ("subgoal 1" :in-theory (enable exactp)
     :use (:instance sigc-enum-v-when-normal
                     (p (P f))
                     (qmin (Qmin f))
                     (b 2))))
   :prep-lemmas
   ((defrule sigc-as-sig
      (equal (sigc x p 2)
             (* (sig x) (expt 2 (1- p))))
      :enable (sigc sig sigm expo-as-expe)))))

(acl2::with-arith5-help
 (defrule nrepp-enum-v
  (implies (and (formatp f)
                (<= (enum-drange (P f) 2) (nfix n))
                (< (nfix n)
                   (+ (enum-drange (P f) 2)
                      (* (1+ (- (Qmax f) (Qmin f)))
                         (enum-nrange (P f) 2)))))
           (nrepp (enum-v n (P f) (Qmin f) 2) f))
  :enable (nrepp)
  :hints
  (("subgoal 3" :in-theory (enable expq expo-as-expe Qmin 2^{W-1}-as-bias)
    :use (:instance expq-enum-v-when-normal
                    (p (P f))
                    (qmin (Qmin f))
                    (b 2)))
   ("subgoal 2" :in-theory (enable P) :use exactp-enum-v)
   ("subgoal 1" :in-theory (enable expq expo-as-expe)
    :use (:instance expq-enum-v-when-normal
                    (p (P f))
                    (qmin (Qmin f))
                    (b 2))))
  :prep-lemmas
  ((acl2::with-arith5-nonlinear-help
    (defrule lemma
     (implies (and (formatp f)
                   (< (nfix n)
                   (+ (enum-drange (P f) 2)
                      (* (1+ (- (Qmax f) (Qmin f)))
                         (enum-nrange (P f) 2)))))
              (<= (enum-q n (P f) (Qmin f) 2)
                  (+ (1- (expt 2 (expw f))) (- (bias f)) (- (P f)))))
     :rule-classes :linear
     :cases ((<= (enum-q n (P f) (Qmin f) 2) (Qmax f)))
     :hints
     (("subgoal 2" :in-theory (enable enum-q Qmax-as-Qmin))
      ("subgoal 1" :in-theory (enable Qmax 2^{W-1} W_ bias))))))))

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
  :enable (round-f-as-rne1 c q-as-expe expo-as-expe))

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
