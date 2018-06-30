#|
(include-book "rtl/rel11/portcullis" :dir :system)
|#
(in-package "RTL")
(include-book "std/basic/arith-equiv-defs" :dir :system)
(include-book "section10")
(include-book "ranges")
(include-book "models")

(local (include-book "std/basic/inductions" :dir :system))
(local (include-book "rtl/rel11/support/basic" :dir :system))
(local (include-book "rtl/rel11/support/float" :dir :system))
(local (include-book "rtl/rel11/support/reps" :dir :system))
(local (acl2::allow-arith5-help))

(acl2::with-arith5-help
 (define sbi
  ((i posp)
   (v pos-rationalp)
   (f formatp))
  :returns (sbi posp :rule-classes :type-prescription)
  (let ((i (min (H f) (acl2::pos-fix i))))
    (* (s_i i v) (expt (D) (- (H f) i))))
  ///
  (fty::deffixequiv sbi)
  (acl2::with-arith5-nonlinear++-help
   (defruled sbi-linear
     (let* ((sbi (sbi i v f))
            (H (H f)))
       (implies (and (posp i)
                     (<= i H))
                (and (<= (expt (D) (- H 1)) sbi)
                     (< (- (* (f v) (expt (D) H)) (expt (D) (- H i)))
                        sbi)
                     (<= sbi (* (f v) (expt (D) H)))
                     (< sbi (expt (D) H)))))
     :rule-classes ((:linear :trigger-terms ((sbi i v f))))
     :use s_i-linear))
  (defrule ordD-sbi
    (implies (and (posp i)
                  (<= i (H f)))
             (equal (ordD (sbi i v f)) (H f)))
    :enable result-1-5)
  (defruled sbi*D^{-g}-as-s_i
    (implies (and (posp i)
                  (integerp -g)
                  (<= -g 0)
                  (= (- i -g) (H f)))
             (equal (* (expt (D) -g) (sbi i v f))
                    (s_i i v))))
  (defruled sbi*D^{e-H}-as-u_i
    (implies (and (posp i)
                  (<= i (H f)))
             (equal (* (expt (D) (+ (- (H f)) (e v))) (sbi i v f))
                    (u_i i v)))
    :enable u_i)))

(acl2::with-arith5-help
 (define tbi
  ((i posp)
   (v pos-rationalp)
   (f formatp))
  :returns (tbi posp :rule-classes :type-prescription)
  (let ((i (min (H f) (acl2::pos-fix i))))
    (* (t_i i v) (expt (D) (- (H f) i))))
  ///
  (fty::deffixequiv tbi)
  (acl2::with-arith5-nonlinear++-help
   (defruled tbi-linear
     (let* ((tbi (tbi i v f))
            (H (H f)))
       (implies (and (posp i)
                     (<= i H))
                (and (< (expt (D) (- H 1)) tbi)
                     (< (* (f v) (expt (D) H)) tbi)
                     (<= tbi (expt (D) H)))))
     :rule-classes ((:linear :trigger-terms ((tbi i v f))))
     :use t_i-linear))
  (defrule ordD-tbi
    (implies (and (posp i)
                  (<= i (H f))
                  (not (equal (tbi i v f) (expt (D) (H f)))))
             (equal (ordD (tbi i v f)) (H f)))
    :use ordD-t_i
    :enable result-1-5)
  (defruled tbi*D^{-g}-as-t_i
    (implies (and (posp i)
                  (integerp -g)
                  (<= -g 0)
                  (= (- i -g) (H f)))
             (equal (* (expt (D) -g) (tbi i v f))
                    (t_i i v))))
  (defruled tbi*D^{e-H}-as-w_i
    (implies (and (posp i)
                  (<= i (H f)))
             (equal (* (expt (D) (+ (- (H f)) (e v))) (tbi i v f))
                    (w_i i v)))
    :enable w_i)
  (defruled tbi-matcher
    (implies (and (natp g)
                  (posp i)
                  (= (+ i g) (H f)))
             (equal (+ (expt (D) g)
                       (sbi i v f))
                    (tbi (- (H f) g) v f)))
    :enable (sbi tbi t_i))
  (defruled tbi-matcher-0
   (equal (+ 1 (sbi (H f) v f))
          (tbi (H f) v f))
   :enable (sbi tbi t_i))))

(acl2::with-arith5-help
 (defrule s_i-as-s_h
   (let ((H (H f)))
     (implies (and (posp i)
                   (<= i H))
              (equal (s_i i v)
                     (fl (/ (s_i H v) (expt (D) (- H i)))))))
   :rule-classes ()
   :enable s_i
   :use (:instance fl/int-rewrite
                   (x (* (f v) (expt (D) (H f))))
                   (n (expt (D) (- (H f) i))))))

(acl2::with-arith5-help
 (defrule sbi-as-sbH
   (let ((H (H f)))
     (implies (and (posp i)
                   (<= i H))
              (equal (sbi i v f)
                     (* (fl (/ (sbi H v f) (expt (D) (- H i))))
                        (expt (D) (- H i))))))
   :rule-classes ()
   :enable (sbi s_i)
   :use (:instance fl/int-rewrite
                   (x (* (f v) (expt (D) (H f))))
                   (n (expt (D) (- (H f) i))))))

(define qb
  ((v pos-rationalp)
   (f formatp))
  :returns (qb integerp :rule-classes ())
  (let ((q (q v f))
        (c (c v f)))
    (if (or (= q (Qmin f)) (not (= c (2^{P-1} f))))
        (- q 1)
      (- q 2)))
  ///
  (fty::deffixequiv qb)
  (defrule qb-linear
    (implies (finite-positive-binary-p (pos-rational-fix v) f)
             (and (<= (1- (Qmin f)) (qb v f))
                  (<= (qb v f) (1- (Qmax f)))))
    :rule-classes :linear
    :enable Qmax-as-Qmin)
  (acl2::with-arith5-help
   (defruled qb-monotone
     (implies (<= (pos-rational-fix v1) (pos-rational-fix v2))
              (<= (qb v1 f) (qb v2 f)))
     :use (:instance q-monotone
                     (x v1)
                     (y v2))
     :cases ((= (q v1 f) (q v2 f)))
     :hints
     (("subgoal 1" :cases ((<= (c v1 f) (c v2 f))))
      ("subgoal 1.2" :in-theory (enable c))
      ("subgoal 1.1" :in-theory (enable q c-as-sigc sigc-lower-bound 2^{P-1}))))))

(define cb
  ((v pos-rationalp)
   (f formatp))
  :returns (cb pos-rationalp :rule-classes ())
  (let ((q (q v f))
        (c (c v f)))
    (if (or (= q (Qmin f)) (not (= c (2^{P-1} f))))
        (* 2 c)
      (* 4 c)))
  ///
  (fty::deffixequiv cb)
  (defrule cb-linear
    (<= (cb v f) (* 4 (2^{P-1} f)))
    :rule-classes :linear)
  (defrule cb-type-when-finite-positive-binary
    (implies (finite-positive-binary-p (pos-rational-fix v) f)
             (and (integerp (cb v f))
                  (< 1 (cb v f))))
    :rule-classes :type-prescription)
  (acl2::with-arith5-help
   (defruled cb*2^qb-as-v
     (equal (* (cb v f) (expt 2 (qb v f)))
            (pos-rational-fix v))
     :enable (qb c))))

(define cbr
  ((v pos-rationalp)
   (f formatp))
  :returns (!cr pos-rationalp :rule-classes ())
  (let ((q (q v f))
        (c (c v f)))
    (if (or (= q (Qmin f)) (not (= c (2^{P-1} f))))
        (+ (cb v f) 1)
      (+ (cb v f) 2)))
  ///
  (fty::deffixequiv cbr)
  (defrule cbr-linear
    (<= (cbr v f) (+ 2 (* 4 (2^{P-1} f))))
    :rule-classes :linear)
  (defrule cbr-type-when-finite-positive-binary
    (implies (finite-positive-binary-p (pos-rational-fix v) f)
             (and (integerp (cbr v f))
                  (< 1 (cbr v f))))
    :rule-classes :type-prescription)
  (acl2::with-arith5-help
   (defruled cbr*2^qb-as-vr
     (equal (* (cbr v f) (expt 2 (qb v f)))
            (vr v f))
     :enable (qb cb c vr))))

(define cbl
  ((v pos-rationalp)
   (f formatp))
  :returns (cbl rationalp :rule-classes ())
  (- (cb v f) 1)
  ///
  (fty::deffixequiv cbl)
  (defrule cbl-linear
    (<= (cbl v f) (+ -1 (* 4 (2^{P-1} f))))
    :rule-classes :linear)
  (defrule cbl-type-when-finite-positive-binary
    (implies (finite-positive-binary-p (pos-rational-fix v) f)
             (posp (cbl v f)))
    :rule-classes :type-prescription)
  (acl2::with-arith5-help
   (defruled cbl*2^qb-as-vl
     (equal (* (cbl v f) (expt 2 (qb v f)))
            (vl v f))
     :enable (qb cb vl-alt)))
  (defruled cbl-matcher
    (equal (1- (cb v f))
           (cbl v f))))

(define T_
  ((v pos-rationalp)
   (f formatp)
   (S pos-rationalp))
  (/ (expt (D) (- (H f) (e v))) (pos-rational-fix S))
  ///
  (fty::deffixequiv T_))

(define vb
  ((v pos-rationalp)
   (S pos-rationalp))
  :returns (!vb pos-rationalp :rule-classes ())
  (* (pos-rational-fix v) (pos-rational-fix S))
  ///
  (fty::deffixequiv vb)
  (acl2::with-arith5-help
   (defruled fl-vb*T-as-sbH
     (implies (pos-rationalp S)
              (equal (fl (* (vb v S) (T_ v f S)))
                     (sbi (H f) v f)))
    :enable (T_ sbi s_i f))))

(define vbl
  ((v pos-rationalp)
   (f formatp)
   (S pos-rationalp))
  :returns (vbl rationalp :rule-classes ())
  (* (vl v f) (pos-rational-fix S))
  ///
  (fty::deffixequiv vbl))

(define vbr
  ((v pos-rationalp)
   (f formatp)
   (S pos-rationalp))
  :returns (!vbr pos-rationalp :rule-classes ())
  (* (vr v f) (pos-rational-fix S))
  ///
  (fty::deffixequiv vbr))

(define ubi
  ((i posp)
   (v pos-rationalp)
   (f formatp)
   (S pos-rationalp))
  :returns (!vr pos-rationalp :rule-classes ())
  (/ (sbi i v f) (T_ v f S))
  ///
  (fty::deffixequiv ubi)
  (defruled ubi-matcher
    (and (equal (/ (sbi i v f) (T_ v f S))
                (ubi i v f S))
         (equal (* (/ (T_ v f S)) (sbi i v f))
                (ubi i v f S))))
  (acl2::with-arith5-help
   (defruled signum-vbl-ubi
     (implies (and (posp i)
                   (<= i (H f))
                   (pos-rationalp S))
              (equal (signum (- (vbl v f S) (ubi i v f S)))
                     (signum (- (vl v f) (u_i i v)))))
     :enable (vbl ubi sbi u_i T_ signum))))

(define wbi
  ((i posp)
   (v pos-rationalp)
   (f formatp)
   (S pos-rationalp))
  :returns (!vr pos-rationalp :rule-classes ())
  (/ (tbi i v f) (T_ v f S))
  ///
  (fty::deffixequiv wbi)
  (defruled wbi-matcher
    (equal (/ (tbi i v f) (T_ v f S))
           (wbi i v f S)))
  (acl2::with-arith5-help
   (defruled signum-wbi-ubr
     (implies (and (posp i)
                   (<= i (H f))
                   (pos-rationalp S))
              (equal (signum (+ (- (vbr v f S)) (wbi i v f S)))
                     (signum (+ (- (vr v f)) (w_i i v)))))
     :enable (vbr wbi tbi w_i T_ signum))))

(acl2::with-arith5-nonlinear-help
 (defruled signum-2*vb-ubi-wbi
   (implies (and (posp i)
                 (<= i (H f))
                 (pos-rationalp S))
            (equal (signum (+ (* 2 (vb v S))
                              (- (ubi i v f S))
                              (- (wbi i v f S))))
                   (signum (+ (* 2 (pos-rational-fix v))
                              (- (u_i i v))
                              (- (w_i i v))))))
   :enable (vb ubi wbi sbi tbi u_i w_i T_ signum)))

(acl2::with-arith5-help
 (define S-full
   ((v pos-rationalp)
    (f formatp))
   :returns (S pos-rationalp :rule-classes ())
   (let* ((e (e v))
          (H (H f))
          (qb (qb v f))
          (pow5 (- H e)))
     (* (expt 2 (max (- qb) pow5))
        (expt (D/2) (max 0 pow5))))
   ///
   (fty::deffixequiv S-full)
   (defrule /T_-type-S-full
     (posp (/ (T_ v f (S-full v f))))
     :rule-classes :type-prescription
     :enable (T_ expt-D-as-expt-D/2))
   (defrule S*2^qb-type-S-full
     (posp (* (S-full v f) (expt 2 (qb v f))))
     :rule-classes :type-prescription)
   (defrule vb-type-S-full
     (implies (finite-positive-binary-p (pos-rational-fix v) f)
              (posp (vb v (S-full v f))))
     :rule-classes :type-prescription
     :enable (vb qb)
     :use (:instance finite-positive-binary-necc
                     (x (pos-rational-fix v))))
   (defrule vbl-type-S-full
     (implies (finite-positive-binary-p (pos-rational-fix v) f)
              (posp (vbl v f (S-full v f))))
     :rule-classes :type-prescription
     :enable (vbl vl-alt qb))
   (defrule vbr-type-S-full
     (implies (finite-positive-binary-p (pos-rational-fix v) f)
              (posp (vbr v f (S-full v f))))
     :rule-classes :type-prescription
     :enable (vbr vr qb))
   (defrule ubi-type-S-full
     (posp (ubi i v f (S-full v f)))
     :rule-classes :type-prescription
     :enable (ubi T_  expt-D-as-expt-D/2))
   (defrule wbi-type-S-full
     (posp (wbi i v f (S-full v f)))
     :rule-classes :type-prescription
     :enable (wbi T_  expt-D-as-expt-D/2))
   (defruled vb-matcher
     (equal (* (cb v f) (S-full v f) (expt 2 (qb v f)))
            (vb v (S-full v f)))
     :enable (vb qb cb c))
   (acl2::with-arith5-help
    (defruled vbr-matcher
      (equal (* (cbr v f) (S-full v f) (expt 2 (qb v f)))
             (vbr v f (S-full v f)))
      :enable (vbr cbr vr cb qb cb c)))
   (acl2::with-arith5-help
    (defruled vbl-matcher
      (equal (* (cbl v f) (S-full v f) (expt 2 (qb v f)))
             (vbl v f (S-full v f)))
      :enable (vbl cbl vl-alt cb qb cb c)))
   (acl2::with-arith5-nonlinear-help
    (defruled vbl-matcher-alt
      (equal (- (vb v (S-full v f))
                (* (S-full v f) (expt 2 (qb v f))))
             (vbl v f (S-full v f)))
      :enable (vbl vl-alt vb qb c)
      :disable S-full))
   (defrule vbl-guard
     (implies (finite-positive-binary-p (pos-rational-fix v) f)
              (<= (* (S-full v f) (expt 2 (qb v f))) (vb v (S-full v f))))
     :rule-classes :linear
     :enable (vb)
     :disable S-full
     :cases ((not (<= (expt 2 (qb v f))
                      (expt 2 (q v f))))
             (not (<= (expt 2 (q v f))
                      (pos-rational-fix v))))
     :hints (("subgoal 2" :in-theory (enable qb))
             ("subgoal 1" :use (:instance finite-positive-binary-necc
                                          (x (pos-rational-fix v))))))))

(acl2::with-arith5-help
 (defruled result-7-part-1
   (let* ((H (H f))
          (e (e v)))
     (implies (and (pos-rationalp v)
                   (< v (MIN_NORMAL f)))
              (<= e H)))
   :rule-classes ((:linear :trigger-terms ((e v))))
   :enable (e H MIN_NORMAL-alt)
   :use (:instance result-1-4
                   (x v)
                   (y (* 2 (2^{P-1} f))))))

(acl2::with-arith5-help
 (defruled result-7-part-2
  (let* ((H (H f))
         (e (e v))
         (qb (qb v f)))
    (implies (and (pos-rationalp v)
                  (finite-positive-binary-p v f)
                  (< v (MIN_NORMAL f)))
             (>= e (+ H qb))))
  :rule-classes ((:linear :trigger-terms ((e v))))
  :cases ((not (=  (+ (H f) (qb v f))
                   (+ -1 (H f) (Qmin f))))
          (not (=  (+ -1 (H f) (Qmin f))
                   (+ (ordD (expt 2 (P f))) (Qmin f))))
          (not (<= (+ (ordD (expt 2 (P f))) (Qmin f))
                   (+ (ordD (expt 2 (- 1 (Qmin f)))) (Qmin f))))
          (not (<= (+ (ordD (expt 2 (- 1 (Qmin f)))) (Qmin f))
                   (ordD (expt 2 (Qmin f)))))
          (not (=  (ordD (expt 2 (Qmin f)))
                   (Emin f)))
          (not (<= (Emin f)
                   (e v))))
  :hints
  (("subgoal 6" :in-theory (enable qb) :use
    ((:instance c-vs-MIN_NORMAL
                   (x v))
     (:instance finite-positive-binary-necc
                (x v))))
   ("subgoal 5" :in-theory (enable H 2^{P-1}))
   ("subgoal 4" :cases ((< (pos-rational-fix (expt 2 (P f)))
                           (pos-rational-fix (expt 2 (- 1 (Qmin f)))))))
   ("subgoal 4.2" :in-theory (enable Qmin))
   ("subgoal 4.1" :in-theory (enable result-1-4))
   ("subgoal 3" :in-theory (enable e Qmin)
    :use (:instance lemma
                    (n (- -2 (Qmin f)))))
   ("subgoal 2" :in-theory (enable Emin e MIN_VALUE))
   ("subgoal 1" :use e-range-when-finite-positive-binary))
  :prep-lemmas
  ((acl2::with-arith5-nonlinear-help
    (defruled lemma1
      (implies (pos-rationalp x)
               (equal (e (* 2 x))
                      (if (< (f x) 1/2) (e x) (1+ (e x)))))
      :enable (f e (D))
      :use ((:instance result-1-3 (k (e x)))
            (:instance result-1-3
                       (x (* 2 x))
                       (k (1+ (e x))))
            (:instance result-1-3
                       (x (* 2 x))
                       (k (e x))))))
   (acl2::with-arith5-nonlinear++-help
    (defruled lemma2
      (implies (pos-rationalp x)
               (equal (e (/ x))
                      (if (= (f x) (/ (D))) (- 2 (e x)) (- 1 (e x)))))
      :enable (f e (D))
      :use ((:instance result-1-3 (k (e x)))
            (:instance result-1-3
                       (x (/ x))
                       (k (- 2 (e x))))
            (:instance result-1-3
                       (x (/ x))
                       (k (- 1 (e x)))))))
   (acl2::with-arith5-nonlinear++-help
    (defruled lemma3
      (implies (pos-rationalp x)
               (equal (e (/ 2 x))
                      (if (<= (f x) (/ 2 (D))) (- 2 (e x)) (- 1 (e x)))))
      :enable (f e (D))
      :use ((:instance result-1-3 (k (e x)))
            (:instance result-1-3
                       (x (/ 2 x))
                       (k (- 2 (e x))))
            (:instance result-1-3
                       (x (/ 2 x))
                       (k (- 1 (e x)))))))
   (acl2::with-arith5-help
    (defrule lemma
      (implies (natp n)
              (<= (e (expt 2 (+ n 3))) (+ 2 n (e (expt 2 (- -2 n))))))
     :induct (acl2::dec-induct n)
     :enable ((D))
     :hints
     (("subgoal *1/2" :use (
       (:instance lemma1 (x (expt 2 (+ n 2))))
       (:instance lemma2 (x (expt 2 (+ n 2))))
       (:instance lemma3 (x (expt 2 (+ n 2))))))))))))

;; Theorems below are for double format only

(define Pred-case-impossible
  ((v pos-rationalp)
   (f formatp))
  :returns (yes booleanp :rule-classes ())
  (let* ((H (H f))
         (e (e v))
         (qb (qb v f)))
    (implies (> e H)
             (<= e (+ H qb))))
  ///
  (fty::deffixequiv Pred-case-impossible))

(define check-range-case-impossible
  ((f formatp)
   (q integerp)
   (c-min posp)
   (c-max posp)
   (ord2 integerp)
   (ordD integerp)
   (qb integerp))
  :returns (yes booleanp :rule-classes ())
  (declare (ignore q c-min c-max ord2))
  (let* ((H (H f))
         (e (ifix ordD))
         (qb (ifix qb)))
    (implies (> e H)
             (<= e (+ H qb))))
  ///
  (fty::deffixequiv check-range-case-impossible)
  (defrule check-range-case-impossible-correct
    (implies (check-range-case-impossible
              f
              (q v f)
              c-min
              c-max
              (ord2 v)
              (ordD v)
              (qb v f))
             (Pred-case-impossible v f))
    :enable (Pred-case-impossible e)))

(define check-ranges-case-impossible
  ((ranges fp-range-list-p))
  :returns (yes booleanp :rule-classes ())
  (or (atom ranges)
      (and (check-range-case-impossible
            (fp-range->f (car ranges))
            (fp-range->q (car ranges))
            (fp-range->c-min (car ranges))
            (fp-range->c-max (car ranges))
            (fp-range->ord2 (car ranges))
            (fp-range->ordD (car ranges))
            (fp-range->qb (car ranges)))
           (check-ranges-case-impossible (cdr ranges))))
  ///
  (fty::deffixequiv check-ranges-case-impossible))

(defrule check-ranges-case-impossible-correct
  (implies (and (valid-fp-ranges-p ranges f)
                (check-ranges-case-impossible ranges)
                (finite-positive-binary-p (pos-rational-fix v) f)
                (consp ranges)
                (or (< (q v f) (fp-range->q (car ranges)))
                    (and (= (q v f) (fp-range->q (car ranges)))
                         (<= (c v f) (fp-range->c-max (car ranges))))))
           (Pred-case-impossible v f))
  :hints (("subgoal 1" :in-theory (enable check-ranges-case-impossible)))
  :use
  (:instance
    (:functional-instance
     check-Pred-on-ranges-correct
     (Pred Pred-case-impossible)
     (check-Pred-on-range check-range-case-impossible)
     (check-Pred-on-ranges check-ranges-case-impossible))
    (v (pos-rational-fix v))))

(defrule case-impossible
   (let* ((f (dp))
          (H (H f))
          (e (e v))
          (qb (qb v f)))
     (implies (and (pos-rationalp v)
                   (finite-positive-binary-p v f)
                   (> e H))
              (<= e (+ H qb))))
   :enable Pred-case-impossible
   :cases ((check-ranges-case-impossible (ranges-dp)))
   :hints (("subgoal 2" :in-theory (enable ranges-dp))
           ("subgoal 1" :use (:instance check-ranges-case-impossible-correct
                                        (ranges (ranges-dp))
                                        (f (dp))))))

(defrule |(+ x (- x) y)|
  (equal (+ x (- x) y) (fix y)))

(defrule nfix-when-natp
  (implies (natp x)
           (equal (nfix x) x)))

(defrule g<64-dp
  (implies (< g (H (dp)))
           (< g 64))
  :enable ((dp)))

(defrule sbyte32p-g-dp
  (implies (and (natp g)
                (< g (H (dp))))
           (acl2::sbyte32p g))
  :enable ((dp)))

(defruled {H-i}-matcher-dp
  (implies (and (posp i)
                (<= i (H (dp))))
           (equal (int-fix (- *H* (acl2::sbyte32-fix i)))
                  (- (H (dp)) i)))
  :enable (acl2::sbyte32p (dp)))

(defruled {e-H}-matcher-dp
  (implies (finite-positive-binary-p (pos-rational-fix v) (dp))
           (equal (int-fix (+ (- *H*) (e v)))
                  (+ (- (H (dp))) (e v))))
  :enable (e-range-when-finite-positive-binary acl2::sbyte32p (dp)))

(defruled {H-e}-matcher-dp
  (implies (finite-positive-binary-p (pos-rational-fix v) (dp))
           (equal (int-fix (- *H* (e v)))
                  (- (H (dp)) (e v))))
  :enable (e-range-when-finite-positive-binary acl2::sbyte32p (dp)))

(defruled G-dp
  (equal (G (dp)) (- (H (dp)) (- *H* *G*)))
  :enable ((dp)))

(defrule G<H
  (< (- *H* *G*) (H (dp)))
  :enable ((dp)))

(defrule sbyte32p-{g-1}-dp
  (implies (and (natp g)
                (< g (H (dp))))
           (acl2::sbyte32p (1- g)))
    :enable (sbyte32-suff (dp)))

;(defrule sbyte32-H-i-dp
;  (implies (and (posp i)
;                (<= i (H (dp))))
;           (acl2::sbyte32p (- (H (dp)) i)))
;  :enable (sbyte32-suff (dp)))
#|
(acl2::with-arith5-nonlinear-help
 (defrule sbyte64p-D^{H-i}-dp
   (implies (and (posp i)
                 (<= i (H (dp))))
            (acl2::sbyte64p (expt (D) (- (H (dp)) i))))
   :enable ((D) (dp) acl2::sbyte64p)
   :cases ((<= (expt (D) (- (H (dp)) i)) (expt (D) (H (dp)))))))
|#
(acl2::with-arith5-help
 (defruled sbyte64p-D^g-dp
   (implies (and (natp g)
                 (<= g (H (dp))))
            (acl2::sbyte64p (expt (D) g)))
   :enable ((D) (dp) acl2::sbyte64p)))

(acl2::with-arith5-help
 (defrule sbyte64p-s_i-dp
   (implies (and (posp i)
                 (<= i (H (dp))))
            (acl2::sbyte64p (s_i i v)))
   :enable ((D) (dp) s_i-linear sbyte64-suff)))

(defrule sbyte32p-qb-dp
   (implies (finite-positive-binary-p (pos-rational-fix v) (dp))
            (acl2::sbyte32p (qb v (dp))))
   :enable (acl2::sbyte32p qb (dp)))

(defrule sbyte64p-cb-dp
  (implies (finite-positive-binary-p (pos-rational-fix v) (dp))
           (acl2::sbyte64p (cb v (dp))))
  :enable (acl2::sbyte64p (dp)))

(defrule sbyte64p-cbl-dp
  (implies (finite-positive-binary-p (pos-rational-fix v) (dp))
           (acl2::sbyte64p (cbl v (dp))))
  :enable (acl2::sbyte64p (dp)))

(defrule sbyte64p-cbr-dp
  (implies (finite-positive-binary-p (pos-rational-fix v) (dp))
           (acl2::sbyte64p (cbr v (dp))))
  :enable (acl2::sbyte64p (dp)))

(defrule sbyte64p-sbi-dp
  (implies (and (posp i)
                (<= i (H (dp))))
           (acl2::sbyte64p (sbi i v (dp))))
  :enable ((dp) (D) acl2::sbyte64p)
  :use (:instance sbi-linear
                  (f (dp))))

(defrule sbyte64p-tbi-dp
  (implies (and (posp i)
                (<= i (H (dp))))
           (acl2::sbyte64p (tbi i v (dp))))
  :enable ((dp) (D))
  :use (:instance tbi-linear
                  (f (dp))))

(defruled logand-s_i-1-as-evenp
  (implies (acl2::sbyte64p s_i)
           (equal (equal (long-fix (logand s_i 1)) 0)
                  (evenp s_i))))

(acl2::with-arith5-help
 (defruled ldiv-as-s_i
   (implies (and (posp i)
                 (natp g)
                 (= (+ i g) (H (dp))))
            (equal (ldiv (sbi i v (dp)) (expt (D) g))
                   (s_i i v)))
   :enable (ldiv-when-nonnegative-args sbi*D^{-g}-as-s_i sbyte64p-D^g-dp)))

(defruled logand-ldiv-sbi-as-evenp-s_i
  (let* ((f (dp))
         (H (H f))
         (i (- H g)))
    (implies
     (and (natp g)
          (< g H))
     (equal (equal (long-fix (logand (ldiv (sbi i v f) (expt (D) g)) 1)) 0)
            (evenp (s_i i v)))))
  :enable (ldiv-as-s_i logand-s_i-1-as-evenp))

(acl2::with-arith5-help
 (defrule lrem-1
   (equal (lrem x 1) 0)
   :enable lrem))

(acl2::with-arith5-help
 (defruled lrem-as-crop
   (implies (and (acl2::sbyte64p x)
                 (acl2::sbyte64p y)
                 (<= 0 x)
                 (< 0 y))
            (equal (long-fix (- x (lrem x y)))
                   (* (fl (/ x y)) y)))
   :enable (long-fix-when-sbyte64 acl2::sbyte64p)
   :use (lrem-when-nonnegative-args
         mod-def
         (:instance fl-def (x (/ x y))))))

(acl2::with-arith5-help
 (defruled lrem-as-sbi-dp
   (acl2::b*
    ((f (dp))
     (H (H f)))
    (implies (and (natp g)
                  (< g (H f)))
             (equal (long-fix (- (sbi H v f)
                                 (lrem (sbi H v f) (expt (D) g))))
                    (sbi (- H g) v f))))
    :enable sbyte64p-D^g-dp
    :use ((:instance lrem-as-crop
                     (x (sbi (H (dp)) v (dp)))
                     (y (expt (D) g)))
          (:instance sbi-as-sbH
                     (i (- (H (dp)) g))
                     (f (dp))))))

(defruled Natural.compareTo-as-signum
  (implies (and (natp this)
                (natp y))
           (equal (Natural.compareTo this y)
                  (signum (- this y))))
  :enable Natural.compareTo)

(defruled Natural.closerTo-as-signum
  (implies (and (natp this)
                (natp x)
                (natp y))
           (equal (Natural.closerTo this x y)
                  (signum (- (* 2 this) (+ x y)))))
  :enable Natural.closerTo)

(defrule Powers.pow10[]-as-expt
    (implies (and (natp g)
                  (<= g (H (dp))))
             (equal (Powers.pow10[] g)
                    (expt (D) g)))
    :enable (Powers.pow10[]-when-i<MAX_POW_10_EXP (dp) (D)))

(defruled DoubleToDecimal.toChars-lemma
  (implies (and (acl2::sbyte64p c)
                (acl2::sbyte32p e))
           (equal (DoubleToDecimal.toChars this c e)
                  (* c (expt (D) (- e (H (dp)))))))
  :enable (DoubleToDecimal.toChars (dp) (D)))

(define common-precondition
  ((this DoubleToDecimal-p)
   (v pos-rationalp))
  :returns (yes booleanp)
  (acl2::b*
   (((DoubleToDecimal this) this)
    (f (dp)))
   (and (finite-positive-binary-p (pos-rational-fix v) f)
        (= this.e (e v))
        (= this.q (q v f))
        (= this.c (c v f))
        (= this.lout (acl2::bool->bit (oddp this.c)))
        (= this.rout (acl2::bool->bit (oddp this.c)))))
  ///
  (fty::deffixequiv common-precondition)
  (defrule common-precondtion-fwd
    (implies (common-precondition this v)
             (finite-positive-binary-p (pos-rational-fix v) (dp)))
    :rule-classes :forward-chaining)
  (defrule this.e-common-precondition
    (acl2::b*
     (((DoubleToDecimal this) this))
     (implies (common-precondition this v)
              (equal this.e (e v)))))
  (defrule Natural.compareTo-vbl-ubi-S-full-as-u-i-in-tau-intervalp
    (acl2::b*
     (((DoubleToDecimal this) this)
      (f (dp))
      (S (S-full v f)))
     (implies (and (common-precondition this v)
                   (pos-rationalp S)
                   (posp i)
                   (<= i (H (dp))))
              (equal (< 0 (int-fix (+ this.lout
                                      (Natural.compareTo (vbl v f S)
                                                         (ubi i v f S)))))
                     (not (in-tau-intervalp (u_i i v) (Rv v f))))))
    :enable (in-tau-intervalp-Rv
             signum-vbl-ubi
             u_i-linear)
    :use (:instance Natural.compareTo-as-signum
                    (this (vbl v (dp) (S-full v (dp))))
                    (y (ubi i v (dp) (S-full v (dp)))))
    :expand (signum (- (vl v (dp)) (u_i i v))))
  (defrule Natural.compareTo-wbi-vbr-S-full-as-u-i-in-tau-intervalp
    (acl2::b*
     (((DoubleToDecimal this) this)
      (f (dp))
      (S (S-full v f)))
     (implies (and (common-precondition this v)
                   (pos-rationalp S)
                   (posp i)
                   (<= i (H (dp))))
              (equal (< 0 (int-fix (+ this.rout
                                      (Natural.compareTo (wbi i v f S)
                                                         (vbr v f S)))))
                     (not (in-tau-intervalp (w_i i v) (Rv v f))))))
    :enable (Natural.compareTo-as-signum
             in-tau-intervalp-Rv
             signum-wbi-ubr
             w_i-linear)
    :expand (signum (+ (- (vr v (dp))) (w_i i v))))
  (acl2::with-arith5-help
   (defrule Natural.closeTo-vb-ubi-ubu-as-abs
     (acl2::b*
      (((DoubleToDecimal this) this)
       (f (dp))
       (S (S-full v f)))
      (implies (and (common-precondition this v)
                    (pos-rationalp S)
                    (posp i)
                    (<= i (H (dp))))
               (equal (Natural.closerTo (vb v S)
                                        (ubi i v f S)
                                        (wbi i v f S))
                      (signum (+ (* 2 (pos-rational-fix v))
                                 (- (u_i i v))
                                 (- (w_i i v)))))))
     :enable (Natural.closerTo-as-signum
              signum-2*vb-ubi-wbi
              u_i-linear w_i-linear)))
  (defrule DoubleToDecimal.toChars-sbi
    (let ((f (dp)))
      (implies (and (common-precondition this v)
                    (posp i)
                    (<= i (H f)))
               (equal (DoubleToDecimal.toChars this (sbi i v f) (e v))
                      (u_i i v))))
    :enable (sbi*D^{e-H}-as-u_i DoubleToDecimal.toChars-lemma))
  (defrule DoubleToDecimal.toChars-tbi
    (let ((f (dp)))
      (implies (and (common-precondition this v)
                    (posp i)
                    (<= i (H f)))
               (equal (DoubleToDecimal.toChars this (tbi i v f) (e v))
                      (w_i i v))))
    :enable (tbi*D^{e-H}-as-w_i DoubleToDecimal.toChars-lemma)))

; fullCaseXS

(define precondition-fullCaseXS
  ((v pos-rationalp))
  :returns (yes booleanp)
  (acl2::b*
   ((f (dp))
    (H (H f))
    (e (e v)))
   (and (<= e H)
        (> e (+ H (qb v f)))))
  ///
  (fty::deffixequiv precondition-fullCaseXS)
  (acl2::with-arith5-help
   (defrule m-fullCaseXS
     (implies (and (finite-positive-binary-p (pos-rational-fix v) (dp))
                   (precondition-fullCaseXS v))
              (equal (Powers.pow5 (int-fix (- *H* (e v))))
                     (expt (D/2) (- (H (dp)) (e v)))))
     :enable (e-range-when-finite-positive-binary
              Powers.pow5 (dp) (D/2) sbyte32-suff)))
  (defrule p-type-fullCaseXS
    (let ((f (dp)))
      (implies (precondition-fullCaseXS v)
               (posp (+ (- (H f)) (e v) (- (qb v f))))))
    :rule-classes :type-prescription)
   (defrule sbyte32p-p-fullCaseXS
     (let ((f (dp)))
       (implies (precondition-fullCaseXS v)
                (acl2::sbyte32p (+ (- (H f)) (e v) (- (qb v f))))))
     :enable (qb (dp) sbyte32-suff))
   (acl2::with-arith5-help
    (defruled T_-match-fullCaseXS
      (let ((f (dp)))
        (implies (precondition-fullCaseXS v)
                 (equal (expt 2 (+ (H f) (- (e v)) (qb v f)))
                        (T_ v f (S-full v f)))))
      :enable (T_ S-full expt-D-as-expt-D/2)))
   (acl2::with-arith5-help
    (defruled /T_-match-fullCaseXS
      (let ((f (dp)))
        (implies (precondition-fullCaseXS v)
                 (equal (expt 2 (+ (- (H f)) (e v) (- (qb v f))))
                        (/ (T_ v f (S-full v f))))))
      :enable (T_ S-full expt-D-as-expt-D/2)))
   (acl2::with-arith5-help
    (defrule S*2^qb-match-fullCaseXS
      (let ((f (dp)))
        (implies (precondition-fullCaseXS v)
                 (equal (expt (D/2) (- (H f) (e v)))
                        (* (S-full v f) (expt 2 (qb v f))))))
      :enable S-full)))

(defrule DoubleToDecimal.fullCaseXS-loop-correct
  (let* ((f (dp))
         (H (H f))
         (S (S-full v f))
         (vb (vb v S))
         (vbl (vbl v f S))
         (vbr (vbr v f S))
         (p (+ (- H) (e v) (- (qb v f))))
         (sbH (sbi H v f)))
   (implies
    (and (common-precondition this v)
         (precondition-fullCaseXS v)
         (natp g)
         (< g H))
    (equal (DoubleToDecimal.fullCaseXS-loop this vb vbl vbr p sbH g)
           (algo1 (- H g) v f))))
  :enable (DoubleToDecimal.fullCaseXS-loop
           algo1-when-in-tau-intervalp-u_i-or-w_i
           lrem-as-sbi-dp logand-ldiv-sbi-as-evenp-s_i
           /T_-match-fullCaseXS
           tbi-matcher ubi-matcher wbi-matcher
           u-or-w-in-Rv-when-i>=H)
 :disable (expt nfix evenp abs))

(defrule DoubleToDecimal.fullCaseXS-correct
  (let* ((f (dp))
         (H (H f))
         (qb (qb v f))
         (cb (cb v f))
         (cb_r (cbr v f)))
    (implies (and (common-precondition this v)
                  (precondition-fullCaseXS v)
                  (posp i)
                  (<= i H))
             (equal (DoubleToDecimal.fullCaseXS this qb cb cb_r i)
                    (algo1 i v f))))
  :enable (DoubleToDecimal.fullCaseXS-loop-correct
           DoubleToDecimal.fullCaseXS
           T_-match-fullCaseXS
           vb-matcher
           vbl-matcher-alt
           vbr-matcher
           fl-vb*T-as-sbH
           {H-i}-matcher-dp
           {e-H}-matcher-dp
           acl2::|(- (- x))|))

; fullCaseXL

(define precondition-fullCaseXL
  ((v pos-rationalp))
  :returns (yes booleanp)
  (acl2::b*
   ((f (dp))
    (H (H f))
    (e (e v)))
   (and (<= e (+ H (qb v f)))
        (> e H)))
  ///
  (fty::deffixequiv precondition-fullCaseXL)
  (acl2::with-arith5-help
   (defrule m-fullCaseXL
     (let ((f (dp)))
       (implies (and (finite-positive-binary-p (pos-rational-fix v) f)
                     (precondition-fullCaseXL v))
                (equal (Powers.pow5 (+ (- (H f)) (e v)))
                       (expt (D/2) (+ (- (H f)) (e v))))))
     :enable (e-range-when-finite-positive-binary
              Powers.pow5 (dp) (D/2) sbyte32-suff)))
  (defrule {e-i}-type
    (let ((f (dp)))
      (implies (and (finite-positive-binary-p (pos-rational-fix v) f)
                    (precondition-fullCaseXL v)
                    (natp g)
                    (< g (H f)))
               (natp (+ (- (H f)) g (e v)))))
    :rule-classes :type-prescription)
  (acl2::with-arith5-help
   (defrule {e-i}-fullCaseXS
     (let ((f (dp)))
       (implies (and (finite-positive-binary-p (pos-rational-fix v) f)
                     (precondition-fullCaseXL v)
                     (natp g)
                     (< g (H f)))
                (equal (Powers.pow5 (int-fix (+ (- (H f)) g (e v))))
                       (expt (D/2) (+ (- (H f)) g (e v))))))
     :enable (e-range-when-finite-positive-binary
              Powers.pow5 (dp) (D/2) sbyte32-suff)))
  (defrule p-type-fullCaseXL
    (let ((f (dp)))
      (implies (precondition-fullCaseXL v)
               (natp (+ (H f) (- (e v)) (qb v f)))))
    :rule-classes :type-prescription)
   (defrule sbyte32p-p-fullCaseXL
     (let ((f (dp)))
       (implies (and (finite-positive-binary-p (pos-rational-fix v) (dp))
                     (precondition-fullCaseXL v))
                (acl2::sbyte32p (+ (H f) (- (e v)) (qb v f)))))
     :enable (qb (dp) sbyte32-suff))
   (acl2::with-arith5-help
    (defruled T_-match-fullCaseXL
      (let ((f (dp)))
        (implies (precondition-fullCaseXL v)
                 (equal (expt (D/2) (+ (H f) (- (e v))))
                        (T_ v f (S-full v f)))))
      :enable (T_ S-full expt-D-as-expt-D/2)))
   (acl2::with-arith5-help
    (defruled /T_-match-fullCaseXL
      (let ((f (dp)))
        (implies (precondition-fullCaseXL v)
                 (equal (expt (D/2) (+ (- (H f)) (e v)))
                        (/ (T_ v f (S-full v f))))))
      :enable (T_ S-full expt-D-as-expt-D/2)))
   (acl2::with-arith5-help
    (defrule wbi-match-fullCaseXL
      (let* ((f (dp))
             (H (H f))
             (S (S-full v f)))
        (implies (and (precondition-fullCaseXL v)
                      (natp g)
                      (< g H))
                 (equal (+ (ubi (- H g) v f S)
                           (* (expt 2 g)
                              (expt (D/2) (+ (- H) g (e v)))))
                        (wbi (- H g) v f S))))
      :enable (e-range-when-finite-positive-binary
               ubi wbi sbi tbi t_i T_ S-full expt-D-as-expt-D/2)))
   (acl2::with-arith5-help
    (defrule S*2^qb-match-fullCaseXL
      (let ((f (dp)))
        (implies (precondition-fullCaseXL v)
                 (equal (expt 2 (+ (H f) (- (e v)) (qb v f)))
                        (* (S-full v f) (expt 2 (qb v f))))))
      :enable S-full)))

(defrule DoubleToDecimal.fullCaseXL-loop-correct
  (let* ((f (dp))
         (H (H f))
         (S (S-full v f))
         (qb (qb v f))
         (vb (vb v S))
         (vbl (vbl v f S))
         (vbr (vbr v f S))
         (m (/ (T_ v f S)))
         (sbH (sbi H v f)))
   (implies
    (and (common-precondition this v)
         (precondition-fullCaseXL v)
         (natp g)
         (< g H))
    (equal (DoubleToDecimal.fullCaseXL-loop this qb vb vbl vbr m sbH g)
           (algo1 (- H g) v f))))
  :enable (DoubleToDecimal.fullCaseXL-loop
           algo1-when-in-tau-intervalp-u_i-or-w_i
           lrem-as-sbi-dp logand-ldiv-sbi-as-evenp-s_i
           /T_-match-fullCaseXL
           {e-H}-matcher-dp
           tbi-matcher ubi-matcher wbi-matcher
           u-or-w-in-Rv-when-i>=H)
  :disable (expt nfix evenp abs acl2::nat-equiv))

(acl2::with-arith5-help
 (defrule DoubleToDecimal.fullCaseXL-correct
   (let* ((f (dp))
          (qb (qb v f))
          (cb (cb v f))
          (cb_r (cbr v f)))
     (implies (and (common-precondition this v)
                   (precondition-fullCaseXL v))
              (equal (DoubleToDecimal.fullCaseXL this qb cb cb_r)
                     (algo1 (G f) v f))))
   :enable (DoubleToDecimal.fullCaseXL-loop-correct
            DoubleToDecimal.fullCaseXL
            /T_-match-fullCaseXL
            vb-matcher
            vbl-matcher
            vbr-matcher
            cbl-matcher
            fl-vb*T-as-sbH
            {H-e}-matcher-dp
            {e-H}-matcher-dp
            G-dp)))

; fullCaseM

(define precondition-fullCaseM
  ((v pos-rationalp))
  :returns (yes booleanp)
  (acl2::b*
   ((f (dp))
    (H (H f))
    (e (e v)))
   (and (<= e (+ H (qb v f)))
        (<= e H)))
  ///
  (fty::deffixequiv precondition-fullCaseM)
  #|
  (acl2::with-arith5-help
   (defrule m-fullCaseXL
     (let ((f (dp)))
       (implies (and (finite-positive-binary-p (pos-rational-fix v) f)
                     (precondition-fullCaseXL v))
                (equal (Powers.pow5 (+ (- (H f)) (e v)))
                       (expt (D/2) (+ (- (H f)) (e v))))))
     :enable (e-range-when-finite-positive-binary
              Powers.pow5 (dp) (D/2) sbyte32-suff)))
  (defrule {e-i}-type
    (let ((f (dp)))
      (implies (and (finite-positive-binary-p (pos-rational-fix v) f)
                    (precondition-fullCaseXL v)
                    (natp g)
                    (< g (H f)))
               (natp (+ (- (H f)) g (e v)))))
    :rule-classes :type-prescription)
  (acl2::with-arith5-help
   (defrule {e-i}-fullCaseXS
     (let ((f (dp)))
       (implies (and (finite-positive-binary-p (pos-rational-fix v) f)
                     (precondition-fullCaseXL v)
                     (natp g)
                     (< g (H f)))
                (equal (Powers.pow5 (int-fix (+ (- (H f)) g (e v))))
                       (expt (D/2) (+ (- (H f)) g (e v))))))
     :enable (e-range-when-finite-positive-binary
              Powers.pow5 (dp) (D/2) sbyte32-suff)))
  (defrule p-type-fullCaseXL
    (let ((f (dp)))
      (implies (precondition-fullCaseXL v)
               (natp (+ (H f) (- (e v)) (qb v f)))))
    :rule-classes :type-prescription)
   (defrule sbyte32p-p-fullCaseXL
     (let ((f (dp)))
       (implies (and (finite-positive-binary-p (pos-rational-fix v) (dp))
                     (precondition-fullCaseXL v))
                (acl2::sbyte32p (+ (H f) (- (e v)) (qb v f)))))
     :enable (qb (dp) sbyte32-suff))
   (acl2::with-arith5-help
    (defruled T_-match-fullCaseXL
      (let ((f (dp)))
        (implies (precondition-fullCaseXL v)
                 (equal (expt (D/2) (+ (H f) (- (e v))))
                        (T_ v f (S-full v f)))))
      :enable (T_ S-full expt-D-as-expt-D/2)))
   (acl2::with-arith5-help
    (defruled /T_-match-fullCaseXL
      (let ((f (dp)))
        (implies (precondition-fullCaseXL v)
                 (equal (expt (D/2) (+ (- (H f)) (e v)))
                        (/ (T_ v f (S-full v f))))))
      :enable (T_ S-full expt-D-as-expt-D/2)))
   (acl2::with-arith5-help
    (defrule wbi-match-fullCaseXL
      (let* ((f (dp))
             (H (H f))
             (S (S-full v f)))
        (implies (and (precondition-fullCaseXL v)
                      (natp g)
                      (< g H))
                 (equal (+ (ubi (- H g) v f S)
                           (* (expt 2 g)
                              (expt (D/2) (+ (- H) g (e v)))))
                        (wbi (- H g) v f S))))
      :enable (e-range-when-finite-positive-binary
               ubi wbi sbi tbi t_i T_ S-full expt-D-as-expt-D/2)))
   (acl2::with-arith5-help
    (defrule S*2^qb-match-fullCaseXL
      (let ((f (dp)))
        (implies (precondition-fullCaseXL v)
                 (equal (expt 2 (+ (H f) (- (e v)) (qb v f)))
                        (* (S-full v f) (expt 2 (qb v f))))))
      :enable S-full))
|#
)
#|
(defrule DoubleToDecimal.fullCaseM-loop-correct
  (let* ((f (dp))
         (H (H f))
         (S (S-full v f))
         (vb (vb v S))
         (vbl (vbl v f S))
         (vbr (vbr v f S)))
   (implies
    (and (common-precondition this v)
         (precondition-fullCaseM v)
         (natp g)
         (< g H))
    (equal (DoubleToDecimal.fullCaseM-loop this vb vbl vbr g)
           (algo1 (- H g) v f))))
  :enable (DoubleToDecimal.fullCaseM-loop
           algo1-when-in-tau-intervalp-u_i-or-w_i
           lrem-as-sbi-dp logand-ldiv-sbi-as-evenp-s_i
           /T_-match-fullCaseXL
           {e-H}-matcher-dp
           tbi-matcher ubi-matcher wbi-matcher
           u-or-w-in-Rv-when-i>=H)
  :disable (expt nfix evenp abs acl2::nat-equiv))

(acl2::with-arith5-help
 (defrule DoubleToDecimal.fullCaseXL-correct
   (let* ((f (dp))
          (qb (qb v f))
          (cb (cb v f))
          (cb_r (cbr v f)))
     (implies (and (common-precondition this v)
                   (precondition-fullCaseXL v))
              (equal (DoubleToDecimal.fullCaseXL this qb cb cb_r)
                     (algo1 (G f) v f))))
   :enable (DoubleToDecimal.fullCaseXL-loop-correct
            DoubleToDecimal.fullCaseXL
            /T_-match-fullCaseXL
            vb-matcher
            vbl-matcher
            vbr-matcher
            cbl-matcher
            fl-vb*T-as-sbH
            {H-e}-matcher-dp
            {e-H}-matcher-dp
            G-dp)))
|#
