#|
(include-book "rtl/rel11/portcullis" :dir :system)
|#
(in-package "RTL")
(include-book "section10")
(include-book "ranges")
(include-book "models")

(local (include-book "rtl/rel11/support/float" :dir :system))
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

