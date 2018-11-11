(in-package "RTL")
(include-book "section1")

(local (include-book "rtl/rel11/support/bits" :dir :system))
(local (include-book "rtl/rel11/support/float" :dir :system))
(local (include-book "rtl/rel11/support/reps" :dir :system))
(local (include-book "rtl/rel11/support/round" :dir :system))
(local (acl2::allow-arith5-help))

;(local (defcong acl2::int-equiv acl2::int-equiv (- x) 1))
;(local (defcong real-equiv real-equiv (- x) 1))

(defruledl minus-ifix
  (equal (- (ifix x))
         (ifix (- x))))

(defruledl minus-realfix
  (equal (- (realfix x))
         (realfix (- x))))

; Section 2 of the paper

(defconst *roundTiedToEven* 'rne)

(define round-f
  ((x real/rationalp)
   (f formatp))
  :returns (v rationalp :rule-classes :type-prescription)
  (acl2::b*
   ((x (realfix x))
    (f (format-fix f)))
   (if (<= (spn f) (abs x))
       (rnd x *roundTiedToEven* (prec f))
     (drnd x *roundTiedToEven* f)))
  ///
  (fty::deffixequiv round-f)
  (defrule round-f-minus
    (equal (round-f (- x) f)
           (- (round-f x f)))
    :enable (rnd-minus drnd-minus)
    :cases ((= (realfix x) 0))
    :hints (("subgoal 1" :in-theory (enable drnd)))))

(define D-length
  ((d integerp))
  :returns (D-length posp :rule-classes :type-prescription
                     :hints (("goal" :in-theory (enable (D))
                              :use (:instance expe-monotone
                                             (b (D))
                                             (x 1)
                                             (y (ifix d))))))
  (+ 1 (expe (ifix d) (D)))
  ///
  (fty::deffixequiv D-length)
  (defrule D-length-minus
    (equal (D-length (- d))
           (D-length d))
    :cases ((integerp d))))

(define D-value
  ((d integerp)
   (i integerp))
  :returns (value rationalp :rule-classes :type-prescription)
  (* (ifix d) (expt (D) i))
  ///
  (fty::deffixequiv D-value)
  (defrule D-value-minis
    (equal (D-value (- d) i)
           (- (D-value d i)))
    :enable acl2::|(* x (- y))|))

(define D-even
  ((d integerp))
  :returns (yes booleanp :rule-classes ())
  (evenp (digitn (abs (ifix d)) 0 (D)))
  ///
  (fty::deffixequiv D-even)
  (acl2::with-arith5-help
   (defruled D-even-as-evenp
     (equal (D-even d)
            (evenp (ifix d)))
     :enable (digitn-rec-0 (D))))
  (defrule D-even-minus
    (equal (D-even (- d))
           (D-even d))
    :enable (D-even-as-evenp
             acl2::|(* x (- y))|
             acl2::|(- (* c x))|
             acl2::integerp-minus-x)))

(define other-worse
  ((c? integerp)
   (q? integerp)
   (c* integerp)
   (q* integerp)
   (f formatp))
  :returns (yes booleanp)
  (acl2::b*
   ((n* (D-length c*))
    (n? (D-length c?))
    (d* (D-value c* q*))
    (d? (D-value c? q?))
    (v (round-f d* f)))
   (implies (and (not (= d* d?))
                 (= (round-f d? f) v))
            (or (= n? 1)
                (> n? n*)
                (and (= n? n*)
                     (or (< (abs (- d* v)) (abs (- d? v)))
                         (and (= (abs (- d* v)) (abs (- d? v)))
                              (D-even c*)
                              (not (D-even c?))))))))
  ///
  (fty::deffixequiv other-worse :hints (("goal" :in-theory (disable ifix))))
  (defruled other-worse-minus
    (equal (other-worse (- c?) q? (- c*) q* f)
           (other-worse c? q? c* q* f))))


(defun-sk all-other-worse (c* q* f)
  (declare (xargs :guard (and (integerp c*)
                              (integerp q*)
                              (formatp f))))
  (forall (c? q?)
            (or (not (integerp c?))
                (not (integerp q?))
                (other-worse c? q? c* q* f)))
  :rewrite (implies (and (all-other-worse c* q* f)
                         (integerp c?)
                         (integerp q?))
                    (other-worse c? q? c* q* f)))
(in-theory (disable all-other-worse))

(defruled all-other-worse-minus
   (implies (and (integerp c*)
                 (integerp q*)
                 (formatp f))
            (equal (all-other-worse (- c*) q* f)
                   (all-other-worse c* q* f)))
   :enable acl2::|(- (- x))|
   :use (lemma
        (:instance lemma
                   (c* (- c*))))
  :prep-lemmas
  ((defruled lemma
     (implies (and (integerp c*)
                   (integerp q*)
                   (formatp f))
              (implies (all-other-worse c* q* f)
                       (all-other-worse (- c*) q* f)))
     :enable acl2::|(- (- x))|
     :use
     ((:instance all-other-worse
                 (c* (- c*)))
      (:instance all-other-worse-necc
                 (c? (- (mv-nth 0 (all-other-worse-witness (- c*) q* f))))
                 (q? (mv-nth 1 (all-other-worse-witness (- c*) q* f))))
      (:instance other-worse-minus
                 (c? (- (mv-nth 0 (all-other-worse-witness (- c*) q* f))))
                 (q? (mv-nth 1 (all-other-worse-witness (- c*) q* f))))))))

(define selected-spec
  ((c integerp)
   (q integerp)
   (v real/rationalp)
   (f formatp))
  :returns (yes booleanp :rule-classes ())
  (acl2::b*
   ((c (ifix c))
    (q (ifix q))
    (d (D-value c q))
    (v (realfix v))
    (f (format-fix f)))
   (and (= (round-f d f) v)
        (<= 2 (D-length c))
        (all-other-worse c q f)))
  ///
  (fty::deffixequiv selected-spec)
  (defruled selected-spec-minus
    (equal (selected-spec (- c) q (- v) f)
           (selected-spec c q v f))
    :use (:instance lemma
                    (c (ifix c))
                    (q (ifix q)))
    :enable minus-ifix
    :prep-lemmas
    ((defruled lemma
       (implies (and (integerp c)
                     (integerp q))
                (equal (selected-spec (- c) q (- v) f)
                       (selected-spec c q v f)))
       :enable all-other-worse-minus))))

(define ord2
  ((x pos-rationalp))
  :returns (ord2 integerp :rule-classes ())
  (let ((x (pos-rational-fix x)))
    (1+ (expe x 2)))
  ///
  (fty::deffixequiv ord2))

(define ordD
  ((x pos-rationalp))
  :returns (ordD integerp :rule-classes ())
  (let ((x (pos-rational-fix x)))
    (1+ (expe x (D))))
  ///
  (fty::deffixequiv ordD))
#|
(acl2::with-arith5-help
 (defrule result-1-1
   (implies (and (real/rationalp x)
                 (integerp m)
                 (integerp n))
            (equal (and (<= m x) (< x n))
                   (and (<= m (fl x)) (< (fl x) n))))
   :rule-classes ()))

(defrule result-1-2
  (implies (and (real/rationalp x)
                (integerp m)
                (integerp n))
           (equal (and (< m x) (<= x n))
                  (and (< m (cg x)) (<= (cg x) n))))
  :rule-classes ())

(defrule result-1-3
  (equal (= k (ordD x))
         (let ((x (pos-rational-fix x)))
           (and (integerp k)
                (<= (expt (D) (- k 1)) x)
                (< x (expt (D) k)))))
  :rule-classes ()
  :enable (ordD expe-lower-bound expe-upper-bound)
  :cases ((= k (ordD x)))
  :use (:instance expe-unique
                  (b (D))
                  (x (pos-rational-fix x))
                  (n (1- k))))

(defrule result-1-3-ord2
  (equal (= k (ord2 x))
         (let ((x (pos-rational-fix x)))
           (and (integerp k)
                (<= (expt 2 (- k 1)) x)
                (< x (expt 2 k)))))
  :rule-classes ()
  :enable (ord2 expe-lower-bound expe-upper-bound)
  :cases ((= k (ord2 x)))
  :use (:instance expe-unique
                  (b 2)
                  (x (pos-rational-fix x))
                  (n (1- k))))

(defrule ordD-1
  (equal (ordD 1) 1)
  :use (:instance result-1-3 (x 1) (k 1)))

(acl2::with-arith5-help
 (defrule ordD-expt-D
   (implies (integerp k)
            (equal (ordD (expt (D) k)) (+ k 1)))
   :use (:instance result-1-3 (x (expt (D) k)) (k (+ k 1)))))

(defrule ordD-D
  (equal (ordD (D)) 2)
  :expand (expt (D) 1)
  :use (:instance ordD-expt-D (k 1)))

(defrule ordD-/D
  (equal (ordD (/ (D))) 0)
  :use (:instance ordD-expt-D (k -1)))

(defruled result-1-4
  (implies (< (pos-rational-fix x)
              (pos-rational-fix y))
           (<= (ordD x)
               (ordD y)))
  :enable ordD
  :use (:instance expe-monotone
                  (b (D))
                  (x (pos-rational-fix x))
                  (y (pos-rational-fix y))))

(acl2::with-arith5-help
 (defruled result-1-5
   (implies (and (pos-rationalp d)
                 (integerp r))
            (equal (ordD (* d (expt (D) r)))
                   (+ r (ordD d))))
   :enable ordD
   :use (:instance expe-shift (b (D)) (x d) (n r))))

(acl2::with-arith5-help
 (defruled result-1-6
  (implies (and (rationalp x)
                (<= 1 x))
           (equal (ordD (fl x)) (ordD x)))
  :enable (ordD pos-rationalp)
  :use ((:instance expe-unique (b (D)) (n (expe (fl x) (D))))
        (:instance expe-lower-bound (b (D)) (x (fl x)))
        (:instance expe-upper-bound (b (D)) (x (fl x)))
        (:instance result-1-1
                   (m (expt (D) (expe (fl x) (D))))
                   (n (expt (D) (1+ (expe (fl x) (D)))))))))
|#
