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
  (defruled sbi*D^{i-H}-as-s_i
    (implies (and (posp i)
                  (<= i (H f)))
             (equal (* (expt (D) (+ (- (H f)) i)) (sbi i v f))
                       (s_i i v))))))

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
    :enable result-1-5)))

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
    (implies (finite-positive-binary-p v f)
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
    (implies (finite-positive-binary-p v f)
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
    (implies (finite-positive-binary-p v f)
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
    (implies (finite-positive-binary-p v f)
             (posp (cbl v f)))
    :rule-classes :type-prescription)
  (acl2::with-arith5-help
   (defruled cbl*2^qb-as-vl
     (equal (* (cbl v f) (expt 2 (qb v f)))
            (vl v f))
     :enable (qb cb vl-alt))))

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
  (fty::deffixequiv vb))

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
    (equal (/ (sbi i v f) (T_ v f S))
           (ubi i v f S))))

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
           (wbi i v f S))))

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
   (defrule vb-type-S-full
     (implies (finite-positive-binary-p v f)
              (posp (vb v (S-full v f))))
     :rule-classes :type-prescription
     :enable (vb qb)
     :use (:instance finite-positive-binary-necc
                     (x v)))
   (defrule vbl-type-S-full
     (implies (finite-positive-binary-p v f)
              (posp (vbl v f (S-full v f))))
     :rule-classes :type-prescription
     :enable (vbl vl-alt qb))
   (defrule vbr-type-S-full
     (implies (finite-positive-binary-p v f)
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
     :enable (wbi T_  expt-D-as-expt-D/2))))

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
    (implies (and (finite-positive-binary-p v f)
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

#|
(acl2::with-arith5-help
 (define S
   ((v pos-rationalp)
    (f formatp))
   :returns (S pos-rationalp :rule-classes ())
   (let ((e (e v))
         (H (H f))
         (qb (qb v f)))
     (if (> e H)
         (expt 2 (- H e)) ; XL or L
       (if (>= (+ H (- e) qb) 0)
           (expt (D) (- H e)) ; M
         (* (expt 2 (- qb)) (expt (D/2) (- H e)))))) ; XS or S
   ///
   (fty::deffixequiv S)))
|#



(define Pred-case-impossible
  ((v pos-rationalp)
   (f formatp))
  :returns (yes booleanp :rule-classes ())
  (let* ((H (H f))
         (e (e v))
         (qb (qb v f)))
    (not (and (< (- H e) 0)
              (< (+ (- H e) qb) 0))))
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
    (not (and (< (- H e) 0)
              (< (+ (- H e) qb) 0))))
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
                (finite-positive-binary-p v f)
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
     (check-Pred-on-ranges check-ranges-case-impossible))))

(defrule case-impossible
   (let* ((f (dp))
          (H (H f))
          (e (e v))
          (qb (qb v f)))
     (implies (and (finite-positive-binary-p v f)
                   (< (- H e) 0))
              (>= (+ (- H e) qb) 0)))
   :enable Pred-case-impossible
   :cases ((check-ranges-case-impossible (ranges-dp)))
   :hints (("subgoal 2" :in-theory (enable ranges-dp))
           ("subgoal 1" :use (:instance check-ranges-case-impossible-correct
                                        (ranges (ranges-dp))
                                        (f (dp))))))
#|
(define algo2-loop-body

(define algo2-
  ((g integerp)
   (v pos-rationalp)
   (f formatp))
  :measure (algo1-measure (- (H f) (nfix g)) v f)
  :guard (
  :returns (g natp :rule-classes ())
  (if (natp g)
  (let ((i (acl2::pos-fix i)))
    (if (and (not (in-tau-intervalp (u_i i v) (Rv v f)))
             (not (in-tau-intervalp (w_i i v) (Rv v f))))
        (algo1-i (+ i 1) v f)
      i))
  ///
  (fty::deffixequiv algo2-i)
|#

(defrule sbyte32-H-i
  (implies (and (posp i)
                (<= i (H (dp))))
           (acl2::sbyte32p (- (H (dp)) i)))
  :enable (sbyte32-suff (dp)))

(acl2::with-arith5-nonlinear-help
 (defrule sbyte64p-D^{H-i}
   (implies (and (posp i)
                 (<= i (H (dp))))
            (acl2::sbyte64p (expt (D) (- (H (dp)) i))))
   :enable ((D) (dp) acl2::sbyte64p)
   :cases ((<= (expt (D) (- (H (dp)) i)) (expt (D) (H (dp)))))))

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

(defruled DoubleToDecimal.toChars-lemma
  (implies (and (acl2::sbyte64p c)
                (acl2::sbyte32p e))
           (equal (DoubleToDecimal.toChars this c e)
                  (* c (expt (D) (- e (H (dp)))))))
  :enable (DoubleToDecimal.toChars (dp) (D)))


(define precond
  ((this DoubleToDecimal-p)
   (v pos-rationalp))
  :returns (yes booleanp)
  (acl2::b*
   (((DoubleToDecimal this) this)
    (f (dp)))
   (and (finite-positive-binary-p v f)
        (= this.e (e v))
        (= this.q (q v f))
        (= this.c (c v f))
        (= this.lout (acl2::bool->bit (oddp this.c)))
        (= this.rout (acl2::bool->bit (oddp this.c)))
        (< (+ (H f) (- (e v)) (qb v f)) 0)
        (>= (- (H f) (e v)) 0)))
  ///
  (defrule precond-v-fwd
    (implies (precond this v)
             (finite-positive-binary-p v (dp)))
    :rule-classes :forward-chaining)
  (defrule finite-positive-binary-p-when-precond
    (implies (precond this v)
             (finite-positive-binary-p v (dp))))
  (defrule this.e-when-precond
    (implies (precond this v)
             (equal (DoubleToDecimal->e this) (e v))))
  (defrule sbyte32p-e-when-precond
    (implies (precond this v)
             (acl2::sbyte32p (e v))))
  (defruled e-linear-when-precond
    (implies (precond this v)
             (and (< (+ (H (dp)) (qb v (dp))) (e v))
                  (<= (e v) (H (dp)))))
    :rule-classes ((:linear :trigger-terms ((e v)))))
  (defruled posp-m-when-precond
    (implies (precond this v)
             (posp (expt (D/2) (- (H (dp)) (e v)))))
    :rule-classes :type-prescription)
  (defrule posp-p-when-precond
    (implies (precond this v)
             (posp (+ (- (H (dp))) (e v) (- (qb v (dp))))))
    :rule-classes :type-prescription)
  (defrule sbyte32p-p-when-precond
    (implies (precond this v)
             (acl2::sbyte32p (+ (- (H (dp))) (e v) (- (qb v (dp))))))
    :enable (sbyte32-suff qb (dp)))
  (acl2::with-arith5-help
   (defrule /T_-match-when-precond
     (let ((f (dp)))
       (implies (precond this v)
                (equal (expt 2 (+ (- (H f)) (e v) (- (qb v f))))
                       (/ (T_ v f (S-full v f))))))
     :enable (T_ S-full expt-D-as-expt-D/2)))
;  (defrule vbl-type-when-precond
;    (implies (precond this v)
;             (posp (vbl v (dp) (S-full v (dp)))))
;    :rule-classes :type-prescription)
  (acl2::with-arith5-help
   (defrule sbi*2^p-when-precond
     (let ((f (dp)))
       (implies (and (precond this v)
                     (posp i)
                     (<= i (H f)))
                (equal (* (sbi i v f)
                          (expt 2 (+ (- (H f)) (e v) (- (qb v f)))))
                       (ubi i v f (S-full v f)))))
     :enable (ubi T_ S-full expt-D-as-expt-D/2)))
  (acl2::with-arith5-help
   (defrule tbi*2^p-when-precond
     (let ((f (dp)))
       (implies (and (precond this v)
                     (posp i)
                     (<= i (H f)))
                (equal (* (tbi i v f)
                          (expt 2 (+ (- (H f)) (e v) (- (qb v f)))))
                     (wbi i v f (S-full v f)))))
     :enable (wbi T_ S-full expt-D-as-expt-D/2)))
  (acl2::with-arith5-help
   (defrule signum-vbl-ubi
     (implies (and (posp i)
                   (<= i (H f))
                   (pos-rationalp S))
              (equal (signum (- (vbl v f S) (ubi i v f S)))
                     (signum (- (vl v f) (u_i i v)))))
     :enable (vbl ubi sbi u_i T_ signum)))
  (acl2::with-arith5-help
   (defrule signum-wbi-vbr
     (implies (and (posp i)
                   (<= i (H f))
                   (pos-rationalp S))
              (equal (signum (+ (- (vbr v f S)) (wbi i v f S)))
                     (signum (+ (- (vr v f)) (w_i i v)))))
     :enable (vbr wbi tbi w_i T_ signum)))
  (acl2::with-arith5-help
   (defrule signum-2*vb-ubi-wbi
     (implies (and (posp i)
                   (<= i (H f))
                   (pos-rationalp S))
              (equal (signum (+ (* 2 (vb v  S))
                                (- (ubi i v f S))
                                (- (wbi i v f S))))
                     (signum (+ (* 2 (pos-rational-fix v))
                                (- (u_i i v))
                                (- (w_i i v))))))
     :enable (vb ubi wbi sbi tbi u_i w_i T_ signum)))
  (defrule signum-vl-u_i-when-precond-and-in-tau-interval
    (implies (precond this v)
             (equal (<= (int-fix (+ (DoubleToDecimal->lout this)
                                    (signum (- (vl v (dp)) (u_i i v)))))
                        0)
                    (in-tau-intervalp (u_i i v) (Rv v (dp)))))
    :enable (in-tau-intervalp-Rv signum u_i-linear))
  (defrule signum-w_i-vr-when-precond-and-in-tau-interval
    (implies (precond this v)
             (equal (<= (int-fix (+ (DoubleToDecimal->rout this)
                                    (signum (+ (- (vr v (dp))) (w_i i v)))))
                        0)
                    (in-tau-intervalp (w_i i v) (Rv v (dp)))))
    :enable (in-tau-intervalp-Rv signum w_i-linear))
  (defrule compareTo-vbl-ubi-when-precond-and-in-tau-interval
    (let* ((f (dp))
           (S (S-full v f)))
      (implies (and (precond this v)
                    (posp i)
                    (<= i (H f)))
               (equal (<= (int-fix (+ (DoubleToDecimal->lout this)
                                      (Natural.compareTo (vbl v f S)
                                                         (ubi i v f S))))
                          0)
                      (in-tau-intervalp (u_i i v) (Rv v f)))))
    :enable Natural.compareTo-as-signum
    :use signum-vl-u_i-when-precond-and-in-tau-interval
    :disable precond)
  (defrule compareTo-wbi-vbr-when-precond-and-in-tau-interval
    (let* ((f (dp))
           (S (S-full v f)))
      (implies (and (precond this v)
                    (posp i)
                    (<= i (H f)))
               (equal (<= (int-fix (+ (DoubleToDecimal->rout this)
                                      (Natural.compareTo (wbi i v f S)
                                                         (vbr v f S))))
                          0)
                      (in-tau-intervalp (w_i i v) (Rv v f)))))
    :enable Natural.compareTo-as-signum
    :use signum-w_i-vr-when-precond-and-in-tau-interval
    :disable precond))

(acl2::with-arith5-help
 (rule
  (let* ((f (dp))
         (S (S-full v f)))
   (implies
    (and (finite-positive-binary-p v f)
         (precond this v)
         (posp i)
         (<= i (H f)))
    (equal
     (DoubleToDecimal.fullCaseXS-loop
      this
      (- (H f) i)
      (sbi (H f) v f)
      (- (e v) (+ (H f) (qb v f)))
      (vb v S)
      (vbl v f S)
      (vbr v f S))
     (algo1 i v f))))
 :induct (algo1-i i v (dp))
 :enable (DoubleToDecimal.fullCaseXS-loop
          DoubleToDecimal.toChars-lemma
          int-fix-when-sbyte32
          long-fix-when-sbyte64
          algo1
          algo1-i
          u_i-linear
          w_i-linear
          ubi-matcher
          wbi-matcher
          )
 :disable (compareTo-vbl-ubi-when-precond-and-in-tau-interval
           compareTo-wbi-vbr-when-precond-and-in-tau-interval
           evenp abs)
 :prep-lemmas
 ((defrule lemma1
    (implies (and (natp g)
                  (<= g (H (dp))))
             (equal (Powers.pow10[] g)
                    (expt (D) g)))
    :enable (Powers.pow10[]-when-i<MAX_POW_10_EXP (dp) (D)))
  (defrule lemma2
    (implies (and (posp i)
                  (<= i (H (dp))))
             (acl2::sbyte64p (sbi i v (dp))))
    :enable ((dp) (D) acl2::sbyte64p)
    :use (:instance sbi-linear
                    (f (dp))))
  (defrule lemma2a
    (implies (and (posp i)
                  (<= i (H (dp))))
             (acl2::sbyte64p (tbi i v (dp))))
    :enable ((dp) (D))
    :use (:instance tbi-linear
                    (f (dp))))
  (defrule lemma2b
    (equal (+ 1 (sbi (H (dp)) v (dp)))
           (tbi (H (dp)) v (dp)))
    :enable (sbi tbi t_i))
  (defrule lemma2c
    (implies (and (natp g)
                  (< g (H (dp))))
             (equal (+ (expt (D) g)
                       (sbi (- (H (dp)) g) v (dp)))
                    (tbi (- (H (dp)) g) v (dp))))
    :enable (sbi tbi t_i))
  (defrule lemma2d
    (implies (and (posp i)
                  (<= i (H (dp))))
             (equal (+ (expt (D) (- (H (dp)) i))
                       (sbi i v (dp)))
                    (tbi i v (dp))))
    :enable (sbi tbi t_i))
  (acl2::with-arith5-help
   (defrule lemma3
     (equal (lrem x 1) 0)
     :enable lrem))
  (acl2::with-arith5-help
   (defruled sbyte64p-expt-D-when<H
     (implies (and (natp g)
                   (<= g (H (dp))))
              (acl2::sbyte64p (expt (D) g)))
     :enable ((D) (dp) acl2::sbyte64p)))
  (acl2::with-arith5-help
   (defrule lemma4
     (implies (and (natp g)
                   (< g (H (dp))))
              (equal (long-fix (- (sbi (H (dp)) v (dp))
                                  (lrem (sbi (H (dp)) v (dp)) (expt (D) g))))
                     (sbi (- (H (dp)) g) v (dp))))
     :enable sbyte64p-expt-D-when<H
     :use ((:instance lrem-as-crop
                      (x (sbi (H (dp)) v (dp)))
                     (y (expt (D) g)))
           (:instance sbi-as-sbH
                    (i (- (H (dp)) g))
                    (f (dp))))))
  (defrule lemma4a
    (implies (and (posp i)
                  (<= i (H (dp))))
             (equal (ldiv (sbi i v (dp))
                          (expt (D) (- (H (dp)) i)))
                    (s_i i v)))
    :enable (ldiv-when-nonnegative-args sbi*D^{i-H}-as-s_i))
  (defrule lemma5
    (implies (and (posp i)
                  (<= i (H (dp))))
             (equal (* (expt (D) (+ (- (H (dp))) (e v)))
                       (sbi i v (dp)))
                    (u_i i v)))
    :enable (sbi u_i))
  (defrule lemma6
    (implies (and (posp i)
                  (<= i (H (dp))))
             (equal (* (expt (D) (+ (- (H (dp))) (e v)))
                       (tbi i v (dp)))
                    (w_i i v)))
    :enable (tbi w_i))
  (acl2::with-arith5-help
   (defruled dlemma1
     (implies (and (posp from-i)
                   (<= (acl2::pos-fix from-i) (H (dp))))
              (acl2::sbyte32p (- (H (dp)) (algo1-i from-i v (dp)))))
     :cases ((not (<= 0 (- (H (dp)) (algo1-i from-i v (dp)))))
             (not (<= (- (H (dp)) (algo1-i from-i v (dp))) (H (dp)))))
     :hints (("subgoal 3" :in-theory (enable dp)))
              :use (:instance sbyte32-suff
                              (x (- (H (dp)) (algo1-i from-i v (dp)))))))
  (defrule lemma7
    (implies (and (posp i)
                  (<= i (H (dp))))
             (acl2::sbyte32p (+ -1 (H (dp)) (- i))))
    :enable (dp acl2::sbyte32p)
                    )
  )
 :hints

 (("subgoal *1/2" :do-not-induct t
   :expand ((algo1-i i v (dp))
            (DoubleToDecimal.fullCaseXS-loop
             this
             (- (H (dp)) i)
             (sbi (H (dp)) v (dp))
             (+ (- (H (dp))) (e v) (- (qb v (dp))))
             (vb v (S-full v (dp)))
             (vbl v (dp) (S-full v (dp)))
             (vbr v (dp) (S-full v (dp)))))
   :use (compareTo-vbl-ubi-when-precond-and-in-tau-interval
         compareTo-wbi-vbr-when-precond-and-in-tau-interval))
  ("subgoal *1/2.12" :in-theory (enable Natural.closerTo-as-signum abs)
   :expand (signum (+ (* 2 v) (- (u_i i v)) (- (w_i i v)))))
  ("subgoal *1/2.11" :in-theory (enable Natural.closerTo-as-signum abs)
   :expand (signum (+ (* 2 v) (- (u_i i v)) (- (w_i i v)))))
  ("subgoal *1/2.10" :in-theory (enable Natural.closerTo-as-signum abs)
   :expand (signum (+ (* 2 v) (- (u_i i v)) (- (w_i i v)))))
  ("subgoal *1/2.8" :in-theory (enable Natural.closerTo-as-signum abs)
   :expand (signum (+ (* 2 v) (- (u_i i v)) (- (w_i i v)))))
  ("subgoal *1/2.7" :in-theory (enable Natural.closerTo-as-signum abs)
   :expand (signum (+ (* 2 v) (- (u_i i v)) (- (w_i i v)))))
  ("subgoal *1/2.6" :in-theory
   (enable Natural.closerTo-as-signum evenp-digitn-f-u_i)
   :expand (evenp (s_i i v)))
  ("subgoal *1/2.4" :in-theory (enable Natural.closerTo-as-signum abs)
   :expand (signum (+ (* 2 v) (- (u_i i v)) (- (w_i i v)))))
  ("subgoal *1/2.3" :in-theory
   (enable Natural.closerTo-as-signum evenp-digitn-f-u_i)
   :expand (evenp (s_i i v)))
  ("subgoal *1/1" :do-not-induct t :cases ((< i (H (dp)))))
  ("subgoal *1/1.2" :in-theory (disable abs algo1-i)
   :cases ((= (algo1-i i v (dp)) i)))
  ("subgoal *1/1.2.1" :in-theory (enable algo1-i))
  ("subgoal *1/1.1"
   :use (compareTo-vbl-ubi-when-precond-and-in-tau-interval
         compareTo-wbi-vbr-when-precond-and-in-tau-interval)))))
