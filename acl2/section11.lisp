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
;(local (include-book "std/basic/inductions" :dir :system))
(local (acl2::allow-arith5-help))

(acl2::with-arith5-help
 (define !s_i
  ((i posp)
   (v pos-rationalp)
   (f formatp))
  :returns (!s_i posp :rule-classes :type-prescription)
  (let ((i (min (H f) (acl2::pos-fix i))))
    (* (s_i i v) (expt (D) (- (H f) i))))
  ///
  (fty::deffixequiv !s_i)
  (acl2::with-arith5-nonlinear++-help
   (defruled !s_i-linear
     (let* ((!s_i (!s_i i v f))
            (H (H f)))
       (implies (and (posp i)
                     (<= i H))
                (and (<= (expt (D) (- H 1)) !s_i)
                     (< (- (* (f v) (expt (D) H)) (expt (D) (- H i)))
                        !s_i)
                     (<= !s_i (* (f v) (expt (D) H)))
                     (< !s_i (expt (D) H)))))
     :rule-classes ((:linear :trigger-terms ((!s_i i v f))))
     :use s_i-linear))
  (defrule ordD-!s_i
    (implies (and (posp i)
                  (<= i (H f)))
             (equal (ordD (!s_i i v f)) (H f)))
    :enable result-1-5)))

(acl2::with-arith5-help
 (define !t_i
  ((i posp)
   (v pos-rationalp)
   (f formatp))
  :returns (!t_i posp :rule-classes :type-prescription)
  (let ((i (min (H f) (acl2::pos-fix i))))
    (* (t_i i v) (expt (D) (- (H f) i))))
  ///
  (fty::deffixequiv !t_i)
  (acl2::with-arith5-nonlinear++-help
   (defruled !t_i-linear
     (let* ((!t_i (!t_i i v f))
            (H (H f)))
       (implies (and (posp i)
                     (<= i H))
                (and (< (expt (D) (- H 1)) !t_i)
                     (< (* (f v) (expt (D) H)) !t_i)
                     (<= !t_i (expt (D) H)))))
     :rule-classes ((:linear :trigger-terms ((!t_i i v f))))
     :use t_i-linear))
  (defrule ordD-!t_i
    (implies (and (posp i)
                  (<= i (H f))
                  (not (equal (!t_i i v f) (expt (D) (H f)))))
             (equal (ordD (!t_i i v f)) (H f)))
    :use ordD-t_i
    :enable result-1-5)))

(acl2::with-arith5-help
 (defrule !s_i-as-!s_H
   (let ((H (H f)))
     (implies (and (posp i)
                   (<= i H))
              (equal (!s_i i v f)
                     (* (fl (/ (!s_i H v f) (expt (D) (- H i))))
                        (expt (D) (- H i))))))
   :rule-classes ()
   :enable (!s_i s_i)
   :use (:instance fl/int-rewrite
                   (x (* (f v) (expt (D) (H f))))
                   (n (expt (D) (- (H f) i))))))

(define !q
  ((v pos-rationalp)
   (f formatp))
  :returns (!q integerp :rule-classes ())
  (let ((q (q v f))
        (c (c v f)))
    (if (or (= q (Qmin f)) (not (= c (2^{P-1} f))))
        (- q 1)
      (- q 2)))
  ///
  (fty::deffixequiv !q)
  (defrule !q-linear
    (implies (finite-positive-binary-p v f)
             (and (<= (1- (Qmin f)) (!q v f))
                  (<= (!q v f) (1- (Qmax f)))))
    :rule-classes :linear
    :enable Qmax-as-Qmin)
  (acl2::with-arith5-help
   (defruled !q-monotone
     (implies (<= (pos-rational-fix v1) (pos-rational-fix v2))
              (<= (!q v1 f) (!q v2 f)))
     :use (:instance q-monotone
                     (x v1)
                     (y v2))
     :cases ((= (q v1 f) (q v2 f)))
     :hints
     (("subgoal 1" :cases ((<= (c v1 f) (c v2 f))))
      ("subgoal 1.2" :in-theory (enable c))
      ("subgoal 1.1" :in-theory (enable q c-as-sigc sigc-lower-bound 2^{P-1}))))))

(define !c
  ((v pos-rationalp)
   (f formatp))
  :returns (!c pos-rationalp :rule-classes ())
  (let ((q (q v f))
        (c (c v f)))
    (if (or (= q (Qmin f)) (not (= c (2^{P-1} f))))
        (* 2 c)
      (* 4 c)))
  ///
  (fty::deffixequiv !c)
  (defrule !c-linear
    (<= (!c v f) (* 4 (2^{P-1} f)))
    :rule-classes :linear)
  (defrule !c-type-when-finite-positive-binary
    (implies (finite-positive-binary-p v f)
             (and (integerp (!c v f))
                  (< 1 (!c v f))))
    :rule-classes :type-prescription)
  (acl2::with-arith5-help
   (defrule !c*2^!q-as-v
     (equal (* (!c v f) (expt 2 (!q v f)))
            (pos-rational-fix v))
     :enable (!q c))))

(define !cr
  ((v pos-rationalp)
   (f formatp))
  :returns (!cr pos-rationalp :rule-classes ())
  (let ((q (q v f))
        (c (c v f)))
    (if (or (= q (Qmin f)) (not (= c (2^{P-1} f))))
        (+ (!c v f) 1)
      (+ (!c v f) 2)))
  ///
  (fty::deffixequiv !cr)
  (defrule !cr-linear
    (<= (!cr v f) (+ 2 (* 4 (2^{P-1} f))))
    :rule-classes :linear)
  (defrule !cr-type-when-finite-positive-binary
    (implies (finite-positive-binary-p v f)
             (and (integerp (!cr v f))
                  (< 1 (!cr v f))))
    :rule-classes :type-prescription)
  (acl2::with-arith5-help
   (defrule !cr*2^!q-as-vr
     (equal (* (!cr v f) (expt 2 (!q v f)))
            (vr v f))
     :enable (!q !c c vr))))

(define !cl
  ((v pos-rationalp)
   (f formatp))
  :returns (!cl rationalp :rule-classes ())
  (- (!c v f) 1)
  ///
  (fty::deffixequiv !cl)
  (defrule !cl-linear
    (<= (!cl v f) (+ -1 (* 4 (2^{P-1} f))))
    :rule-classes :linear)
  (defrule !cl-type-when-finite-positive-binary
    (implies (finite-positive-binary-p v f)
             (posp (!cl v f)))
    :rule-classes :type-prescription)
  (acl2::with-arith5-help
   (defrule !cl*2^!q-as-vl
     (equal (* (!cl v f) (expt 2 (!q v f)))
            (vl v f))
     :enable (!q !c vl-alt))))

(acl2::with-arith5-help
 (define S
   ((v pos-rationalp)
    (f formatp))
   :returns (S pos-rationalp :rule-classes ())
   (let ((e (e v))
         (H (H f))
         (!q (!q v f)))
     (if (> e H)
         (expt 2 (- H e)) ; XL or L
       (if (>= (+ H (- e) !q) 0)
           (expt (D) (- H e)) ; M
         (* (expt 2 (- !q)) (expt (D/2) (- H e)))))) ; XS or S
   ///
   (fty::deffixequiv S)))

(acl2::with-arith5-help
 (define T_
   ((v pos-rationalp)
    (f formatp))
   :returns (T_ pos-rationalp :rule-classes ())
   (/ (expt (D) (- (H f) (e v))) (S v f))
   ///
   (fty::deffixequiv T_)))

(define vb
  ((v pos-rationalp)
   (f formatp))
  :returns (!vb pos-rationalp :rule-classes ())
  (* (pos-rational-fix v) (S v f))
  ///
  (fty::deffixequiv vb))

(define vbl
  ((v pos-rationalp)
   (f formatp))
  :returns (!vbl rationalp :rule-classes ())
  (* (vl v f) (S v f))
  ///
  (fty::deffixequiv vbl))

(define vbr
  ((v pos-rationalp)
   (f formatp))
  :returns (!vbr pos-rationalp :rule-classes ())
  (* (vr v f) (S v f))
  ///
  (fty::deffixequiv vbr))

(define !u_i
  ((i posp)
   (v pos-rationalp)
   (f formatp))
  :returns (!vr pos-rationalp :rule-classes ())
  (* (u_i i v) (S v f))
  ///
  (fty::deffixequiv !u_i))

(define !w_i
  ((i posp)
   (v pos-rationalp)
   (f formatp))
  :returns (!vr pos-rationalp :rule-classes ())
  (* (w_i i v) (S v f))
  ///
  (fty::deffixequiv !w_i))

(defruled result-7-part-1-dp
  (let* ((f (dp))
         (H (H f))
         (e (e v)))
    (implies (and (pos-rationalp v)
                  (< v (MIN_NORMAL f)))
             (<= e H)))
  :enable (e (dp))
  :use (:instance result-1-4
                  (x v)
                  (y (MIN_NORMAL (dp)))))

(defruled result-7-part-2-dp
  (let* ((f (dp))
         (H (H f))
         (e (e v))
         (!q (!q v f)))
    (implies (and (finite-positive-binary-p v f)
                  (< v (MIN_NORMAL f)))
             (< (+ H (- e) !q) 0)))
  :enable (e !q (dp))
  :use ((:instance finite-positive-binary-necc
                   (x v)
                   (f (dp)))
        (:instance c-vs-MIN_NORMAL
                   (x v)
                   (f (dp)))
        (:instance result-1-4
                   (x (MIN_VALUE (dp)))
                   (y v))))

(define Pred-case-impossible
  ((v pos-rationalp)
   (f formatp))
  :returns (yes booleanp :rule-classes ())
  (let* ((H (H f))
         (e (e v))
         (!q (!q v f)))
    (not (and (< (- H e) 0)
              (< (+ (- H e) !q) 0))))
  ///
  (fty::deffixequiv Pred-case-impossible))

(define check-range-case-impossible
  ((f formatp)
   (q integerp)
   (c-min posp)
   (c-max posp)
   (ord2 integerp)
   (ordD integerp)
   (!q integerp))
  :returns (yes booleanp :rule-classes ())
  (declare (ignore q c-min c-max ord2))
  (let* ((H (H f))
         (e (ifix ordD))
         (!q (ifix !q)))
    (not (and (< (- H e) 0)
              (< (+ (- H e) !q) 0))))
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
              (!q v f))
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
            (fp-range->!q (car ranges)))
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
          (!q (!q v f)))
     (implies (and (finite-positive-binary-p v f)
                   (< (- H e) 0))
              (>= (+ (- H e) !q) 0)))
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

(acl2::with-arith5-nonlinear++-help
 (defruled lrem-as-mod
   (implies (and (acl2::sbyte64p x)
                 (acl2::sbyte64p y)
                 (<= 0 x)
                 (< 0 y))
            (equal (lrem x y) (mod x y)))
   :enable (lrem acl2::sbyte64p long-fix-when-sbyte64)
   :use (:instance mod-bnd-1
                   (m x)
                   (n y))
   :cases ((acl2::sbyte64p (mod x y)))))

(acl2::with-arith5-help
 (defruled lrem-as-crop
   (implies (and (acl2::sbyte64p x)
                 (acl2::sbyte64p y)
                 (<= 0 x)
                 (< 0 y))
            (equal (long-fix (- x (lrem x y)))
                   (* (fl (/ x y)) y)))
   :enable (long-fix-when-sbyte64 acl2::sbyte64p)
   :use ((:instance lrem-as-mod)
         (:instance mod-def)
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
        (< (+ (H f) (- (e v)) (!q v f)) 0)
        (>= (- (H f) (e v)) 0)))
  ///
  (defrule precond-v-fwd
    (implies (precond this v)
             (pos-rationalp v))
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
             (and (< (+ (H (dp)) (!q v (dp))) (e v))
                  (<= (e v) (H (dp)))))
    :rule-classes ((:linear :trigger-terms ((e v)))))
  (defruled posp-m-when-precond
    (implies (precond this v)
             (posp (expt (D/2) (- (H (dp)) (e v)))))
    :rule-classes :type-prescription)
  (defrule posp-p-when-precond
    (implies (precond this v)
             (posp (+ (- (H (dp))) (e v) (- (!q v (dp))))))
    :rule-classes :type-prescription)
  (defrule sbyte32p-p-when-precond
    (implies (precond this v)
             (acl2::sbyte32p (+ (- (H (dp))) (e v) (- (!q v (dp))))))
    :enable (sbyte32-suff !q (dp)))
  #|
  (acl2::with-arith5-help
   (defrule vb-type
     (implies (precond this v)
              (posp (vb v (dp))))
     :rule-classes :type-prescription
     :enable (finite-positive-binary-p vb S !q)
     :cases ((posp (c v (dp))))
     :hints (("subgoal 2" :use (:instance C-TYPE-WHEN-FINITE-POSITIVE-BINARY
                                          (x v)
                                          (f (dp)))))))
|#
  (acl2::with-arith5-help
   (defrule vbl-type
    (implies (precond this v)
             (posp (vbl v (dp))))
    :rule-classes :type-prescription
    :enable (vbl vl-alt S !q)
    :cases ((posp (c v (dp))))
    :hints (("subgoal 2" :use (:instance C-TYPE-WHEN-FINITE-POSITIVE-BINARY
                                         (x v)
                                         (f (dp)))))))
  (acl2::with-arith5-help
   (defrule vbr-type
    (implies (precond this v)
             (posp (vbr v (dp))))
    :rule-classes :type-prescription
    :enable (vbr vr S !q)
    :cases ((posp (c v (dp))))
    :hints (("subgoal 2" :use (:instance C-TYPE-WHEN-FINITE-POSITIVE-BINARY
                                         (x v)
                                         (f (dp)))))))
  (acl2::with-arith5-help
   (defruled expt-D-as-expt-D/2
     (equal (expt (D) k)
            (* (expt 2 k) (expt (D/2) k)))
     :enable D))
  (acl2::with-arith5-help
   (defrule !u_i-type
     (implies (and (precond this v)
                   (posp i)
                   (<= i (H (dp))))
              (posp (!u_i i v (dp))))
     :rule-classes :type-prescription
     :enable (!u_i u_i S expt-D-as-expt-D/2)))
  (acl2::with-arith5-help
   (defrule !w_i-type
     (implies (and (precond this v)
                   (posp i)
                   (<= i (H (dp))))
              (posp (!w_i i v (dp))))
     :rule-classes :type-prescription
     :enable (!w_i w_i S expt-D-as-expt-D/2)))
  (acl2::with-arith5-help
   (defrule !s_i*2^p-when-precond
     (implies (and (precond this v)
                   (posp i)
                   (<= i (H (dp))))
              (equal (* (!s_i i v (dp))
                        (expt 2 (+ (- (H (dp))) (e v) (- (!q v (dp))))))
                     (!u_i i v (dp))))
     :enable (!s_i !u_i u_i S expt-D-as-expt-D/2)))
  (acl2::with-arith5-help
   (defrule !t_i*2^p-when-precond
     (implies (and (precond this v)
                   (posp i)
                   (<= i (H (dp))))
              (equal (* (!t_i i v (dp))
                        (expt 2 (+ (- (H (dp))) (e v) (- (!q v (dp))))))
                     (!w_i i v (dp))))
     :enable (!t_i !w_i w_i S expt-D-as-expt-D/2)))
  (acl2::with-arith5-help
   (defrule signum-vbl-!u_i
     (equal (signum (- (vbl v f) (!u_i i v f)))
            (signum (- (vl v f) (u_i i v))))
     :enable (vbl !u_i signum)))
  (acl2::with-arith5-help
   (defrule signum-!w_i-vbr
     (equal (signum (+ (- (vbr v f)) (!w_i i v f)))
            (signum (+ (- (vr v f)) (w_i i v))))
     :enable (vbr !w_i signum)))
  (acl2::with-arith5-help
   (defrule signum-2*vb-!u_i-!w_i
     (implies (precond this v)
              (equal (signum (+ (* 2 (vb v (dp))) (- (!u_i i v (dp))) (- (!w_i i v (dp)))))
                     (signum (+ (* 2 v) (- (u_i i v)) (- (w_i i v))))))
     :enable (vb !u_i !w_i signum)))
  (acl2::with-arith5-help
   (defrule signum-!u_i-!w_i
     (implies (precond this v)
              (equal (signum (+ (- (!u_i i v (dp))) (- (!w_i i v (dp)))))
                     (signum (+ (- (u_i i v)) (- (w_i i v))))))
     :enable (vb !u_i !w_i signum)))
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
  (defrule compareTo-vbl-!u_i-when-precond-and-in-tau-interval
    (implies (and (precond this v)
                  (posp i)
                  (<= i (H (dp))))
             (equal (<= (int-fix (+ (DoubleToDecimal->lout this)
                                    (Natural.compareTo (vbl v (dp))
                                                       (!u_i i v (dp)))))
                        0)
                    (in-tau-intervalp (u_i i v) (Rv v (dp)))))
    :enable Natural.compareTo-as-signum
    :disable precond)
  (defrule compareTo-vbl-!u_i-when-precond-and-in-tau-interval-corr
    (implies
     (and (precond this v)
          (natp g)
          (< g (H (dp))))
     (equal (<= (int-fix (+ (DoubleToDecimal->lout this)
                            (Natural.compareTo (vbl v (dp))
                                               (!u_i (- (H (dp)) g) v (dp)))))
                0)
            (in-tau-intervalp (u_i (- (H (dp)) g) v) (Rv v (dp)))))
    :use (:instance compareTo-vbl-!u_i-when-precond-and-in-tau-interval
                    (i (- (H (dp)) g))))
  (defrule compareTo-!w_i-vbr-when-precond-and-in-tau-interval
    (implies (and (precond this v)
                  (posp i)
                  (<= i (H (dp))))
             (equal (<= (int-fix (+ (DoubleToDecimal->rout this)
                                    (Natural.compareTo (!w_i i v (dp))
                                                       (vbr v (dp)))))
                        0)
                    (in-tau-intervalp (w_i i v) (Rv v (dp)))))
    :enable Natural.compareTo-as-signum
    :disable precond))
#|
(acl2::with-arith5-help
 (rule
 (let ((f (dp)))
   (implies
    (and (finite-positive-binary-p v f)
         (precond this v)
         (posp i)
         (<= i (H f)))
    (equal
     (DoubleToDecimal.fullCaseXS-loop
      this
      (- (H f) i)
      (!s_i (H f) v f)
      (- (e v) (+ (H f) (!q v f)))
      (vb v f )
      (vbl v f)
      (vbr v f))
     (algo1 i v f))))
 :induct (algo1-i i v (dp))
 :enable (DoubleToDecimal.fullCaseXS-loop
          int-fix-when-sbyte32
          long-fix-when-sbyte64
          algo1
          algo1-i
          sbyte32-suff)
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
             (acl2::sbyte64p (!s_i i v (dp))))
    :enable ((dp) (D) acl2::sbyte64p)
    :use (:instance !s_i-linear
                    (f (dp))))
  (defrule lemma2a
    (implies (and (posp i)
                  (<= i (H (dp))))
             (acl2::sbyte64p (!t_i i v (dp))))
    :enable ((dp) (D))
    :use (:instance !t_i-linear
                    (f (dp))))
  (defrule lemma2b
    (equal (+ 1 (!s_i (H (dp)) v (dp)))
           (!t_i (H (dp)) v (dp)))
    :enable (!s_i !t_i t_i))
  (defrule lemma2c
    (implies (and (natp g)
                  (< g (H (dp))))
             (equal (+ (expt (D) g)
                       (!s_i (- (H (dp)) g) v (dp)))
                    (!t_i (- (H (dp)) g) v (dp))))
    :enable (!s_i !t_i t_i))
  (defrule lemma2d
    (implies (and (posp i)
                  (<= i (H (dp))))
             (equal (+ (expt (D) (- (H (dp)) i))
                       (!s_i i v (dp)))
                    (!t_i i v (dp))))
    :enable (!s_i !t_i t_i))
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
              (equal (long-fix (- (!s_i (H (dp)) v (dp))
                                  (lrem (!s_i (H (dp)) v (dp)) (expt (D) g))))
                     (!s_i (- (H (dp)) g) v (dp))))
     :enable sbyte64p-expt-D-when<H
     :use ((:instance lrem-as-crop
                      (x (!s_i (H (dp)) v (dp)))
                     (y (expt (D) g)))
           (:instance !s_i-as-!s_H
                    (i (- (H (dp)) g))
                    (f (dp))))))
  (defrule lemma5
    (implies (and (posp i)
                  (<= i (H (dp))))
             (equal (* (EXPT (D) (+ (- (H (DP))) (E V)))
                       (!S_I I V (DP)))
                    (u_i i v)))
    :enable (!s_i u_i))
  (defrule lemma6
    (implies (and (posp i)
                  (<= i (H (dp))))
             (equal (* (EXPT (D) (+ (- (H (DP))) (E V)))
                       (!t_I I V (DP)))
                    (w_i i v)))
    :enable (!t_i w_i))
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
  )
 :hints

 (;;("subgoal *1/9" :by lemma-9)
  ;("subgoal *1/8" :by lemma-8)
  ;("subgoal *1/7" :by lemma-7)
  ;("subgoal *1/5" :by lemma-5)
  ;("subgoal *1/4" :by lemma-4)
  ;("subgoal *1/3" :by lemma-3)
  ("subgoal *1/2" :do-not-induct t
   :expand ((algo1-i i v (dp))
            (DOUBLETODECIMAL.FULLCASEXS-LOOP THIS (+ (H (DP)) (- I))
                                       (!S_I (H (DP)) V (DP))
                                       (+ (- (H (DP))) (E V) (- (!Q V (DP))))
                                       (VB V (DP))
                                       (VBL V (DP))
                                       (VBR V (DP)))))
  ("subgoal *1/2.84" :in-theory
   (e/d (DoubleToDecimal.toChars-lemma)
        (compareTo-vbl-!u_i-when-precond-and-in-tau-interval
         compareTo-!w_i-vbr-when-precond-and-in-tau-interval))
   :use (compareTo-vbl-!u_i-when-precond-and-in-tau-interval
         compareTo-!w_i-vbr-when-precond-and-in-tau-interval))
  ("subgoal *1/2.83" :in-theory
   (e/d (DoubleToDecimal.toChars-lemma)
        (compareTo-vbl-!u_i-when-precond-and-in-tau-interval
         compareTo-!w_i-vbr-when-precond-and-in-tau-interval))
   :use (compareTo-vbl-!u_i-when-precond-and-in-tau-interval
         compareTo-!w_i-vbr-when-precond-and-in-tau-interval))
  ("subgoal *1/2.82" :in-theory
   (e/d (DoubleToDecimal.toChars-lemma
         Natural.closerTo-as-signum)
        (compareTo-vbl-!u_i-when-precond-and-in-tau-interval
         compareTo-!w_i-vbr-when-precond-and-in-tau-interval))
   :expand (SIGNUM (+ (* 2 V) (- (U_I I V)) (- (W_I I V))))
   :use (compareTo-vbl-!u_i-when-precond-and-in-tau-interval
         compareTo-!w_i-vbr-when-precond-and-in-tau-interval))
  ("subgoal *1/2.81" :in-theory
   (e/d (DoubleToDecimal.toChars-lemma
         Natural.closerTo-as-signum
         u_i-linear)
        (compareTo-vbl-!u_i-when-precond-and-in-tau-interval
         compareTo-!w_i-vbr-when-precond-and-in-tau-interval))
   :expand (SIGNUM (+ (* 2 V) (- (U_I I V)) (- (W_I I V))))
   :use (compareTo-vbl-!u_i-when-precond-and-in-tau-interval
         compareTo-!w_i-vbr-when-precond-and-in-tau-interval))
  ("subgoal *1/2.80" :in-theory
   (e/d (DoubleToDecimal.toChars-lemma
         Natural.closerTo-as-signum
         u_i-linear)
        (compareTo-vbl-!u_i-when-precond-and-in-tau-interval
         compareTo-!w_i-vbr-when-precond-and-in-tau-interval))
   :expand (SIGNUM (+ (* 2 V) (- (U_I I V)) (- (W_I I V))))
   :use (compareTo-vbl-!u_i-when-precond-and-in-tau-interval
         compareTo-!w_i-vbr-when-precond-and-in-tau-interval))
  ("subgoal *1/2.79" :in-theory
   (e/d (DoubleToDecimal.toChars-lemma
         Natural.closerTo-as-signum
         w_i-linear)
        (compareTo-vbl-!u_i-when-precond-and-in-tau-interval
         compareTo-!w_i-vbr-when-precond-and-in-tau-interval))
   :expand (SIGNUM (+ (* 2 V) (- (U_I I V)) (- (W_I I V))))
   :use (compareTo-vbl-!u_i-when-precond-and-in-tau-interval
         compareTo-!w_i-vbr-when-precond-and-in-tau-interval))
  ("subgoal *1/2.78" :in-theory
   (e/d (DoubleToDecimal.toChars-lemma
         Natural.closerTo-as-signum
         u_i-linear)
        (compareTo-vbl-!u_i-when-precond-and-in-tau-interval
         compareTo-!w_i-vbr-when-precond-and-in-tau-interval))
   :expand (SIGNUM (+ (* 2 V) (- (U_I I V)) (- (W_I I V))))
   :use (compareTo-vbl-!u_i-when-precond-and-in-tau-interval
         compareTo-!w_i-vbr-when-precond-and-in-tau-interval))
  ("subgoal *1/2.1077" :in-theory
   (e/d (DoubleToDecimal.toChars-lemma
         Natural.closerTo-as-signum
         u_i-linear)
        (compareTo-vbl-!u_i-when-precond-and-in-tau-interval
         compareTo-!w_i-vbr-when-precond-and-in-tau-interval))
   :expand (SIGNUM (+ (* 2 V) (- (U_I I V)) (- (W_I I V))))
   :use (compareTo-vbl-!u_i-when-precond-and-in-tau-interval
         compareTo-!w_i-vbr-when-precond-and-in-tau-interval))
  ("subgoal *1/2.1076" :in-theory
   (e/d (DoubleToDecimal.toChars-lemma
         Natural.closerTo-as-signum
         u_i-linear w_i-linear)
        (compareTo-vbl-!u_i-when-precond-and-in-tau-interval
         compareTo-!w_i-vbr-when-precond-and-in-tau-interval))
   :expand (SIGNUM (+ (- (U_I I V)) (- (W_I I V))))
   :use (compareTo-vbl-!u_i-when-precond-and-in-tau-interval
         compareTo-!w_i-vbr-when-precond-and-in-tau-interval))
;  ("subgoal *1/2.26" :in-theory (enable (dp)))
;("subgoal 24.11" :use
  ; compareTo-vbl-!u_i-when-precond-and-in-tau-interval-corr)
  ;("subgoal 24.10"); :in-theory (enable algo1 f !s_i u_i))
  ; ((:instance compareTo-vbl-!u_i-when-precond-and-in-tau-interval
  ;             (i (H (dp))))
  ;  (:instance compareTo-!w_i-vbr-when-precond-and-in-tau-interval
  ;             (i (H (dp))))))
  ;("subgoal 8.20" :use
  ; ((:instance compareTo-vbl-!u_i-when-precond-and-in-tau-interval
  ;             (i (H (dp))))
  ;  (:instance compareTo-!w_i-vbr-when-precond-and-in-tau-interval
  ;             (i (H (dp))))))
 ; ("subgoal 8.19" :in-theory (enable algo1
 ;                                    !s_i f
 ;                                    ))
;   ((:instance compareTo-vbl-!u_i-when-precond-and-in-tau-interval
;               (i (H (dp))))
;    (:instance compareTo-!w_i-vbr-when-precond-and-in-tau-interval
;               (i (H (dp))))))
;
;          :use (:instance lemma2
;                                         (i (H (dp))))))
 )
)

 :do-not-induct t
 )
|#
