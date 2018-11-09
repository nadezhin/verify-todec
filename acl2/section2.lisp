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

(define recover
  ((d integerp)
   (i integerp)
   (f formatp))
  :returns (v rationalp :rule-classes :type-prescription)
  (acl2::b*
   ((d (ifix d))
    (i (ifix i))
    (f (format-fix f))
    (dv (* d (expt (D) i))))
   (if (<= (spn f) (abs dv))
       (rnd dv *roundTiedToEven* (prec f))
     (drnd dv *roundTiedToEven* f)))
  ///
  (fty::deffixequiv recover)
  (acl2::with-arith5-help
   (defrule recover-minus
     (equal (recover (- d) i f)
            (- (recover d i f)))
     :enable (rnd-minus drnd-minus)
     :cases ((zip d))
     :hints (("subgoal 1" :in-theory (enable drnd))))))

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
  (* (ifix d) (expt 2 i))
  ///
  (fty::deffixequiv D-value)
  (acl2::with-arith5-help
   (defrule D-value-minis
     (equal (D-value (- d) i)
            (- (D-value d i))))))

(define D-even
  ((d integerp))
  :returns (yes booleanp :rule-classes ())
  (evenp (digitn (abs (ifix d)) 0 (D)))
  ///
  (fty::deffixequiv D-even)
  (acl2::with-arith5-help
  (defruled D-even-as-eveno
    (equal (D-even d)
           (evenp (ifix d)))
    :enable (digitn-rec-0 (D)))
  (defrule D-even-minus
    (equal (D-even (- d))
           (D-even d)))))

(define better
  ((d1 integerp)
   (i1 integerp)
   (d2 integerp)
   (i2 integerp)
   (v real/rationalp))
  :returns (better booleanp :rule-classes ())
  (acl2::b*
   ((v (realfix v)))
   (or (< (D-length d1)
          (D-length d2))
       (and (= (D-length d1)
               (D-length d2))
            (< (abs (- (D-value d1 i1) v))
               (abs (- (D-value d2 i2) v))))
       (and (= (D-length d1)
               (D-length d2))
            (= (abs (- (D-value d1 i1) v))
               (abs (- (D-value d2 i2) v)))
            (D-even d1)
            (not (D-even d2)))))
  ///
  (fty::deffixequiv better :hints (("goal" :in-theory (disable ifix))))
  (acl2::with-arith5-help
   (defruled better-minus
     (equal (better d1 i1 d2 i2 (- v))
            (better (- d1) i1 (- d2) i2 v))
     :use (:instance lemma
                     (d1 (ifix d1))
                     (d2 (ifix d2))
                     (v (realfix v)))
     :enable (minus-ifix minus-realfix)
     :prep-lemmas
     ((defrule lemma
        (implies (and (integerp d1)
                      (integerp d2)
                      (real/rationalp v))
                 (equal (better d1 i1 d2 i2 (- v))
                        (better (- d1) i1 (- d2) i2 v))))))))

(defun-sk exists-better (d* i* f minlen)
  (declare (xargs :guard (and (integerp d*)
                              (integerp i*)
                              (formatp f)
                              (posp minlen))))
  (exists (d? i?)
          (let ((v (recover d* i* f)))
            (and (integerp d?)
                 (integerp i?)
                 (<= minlen (D-length d?))
                 (= (recover d? i? f) v)
                 (better d? i? d* i* v)))))
(in-theory (disable exists-better))

(acl2::with-arith5-help
 (defruled exists-better-minus
   (implies (and (integerp d*)
                 (integerp i*)
                 (formatp f)
                 (posp minlen))
            (implies (exists-better (- d*) i* f minlen)
                     (exists-better d* i* f minlen)))
   :enable better-minus
   :use
   ((:instance exists-better
               (d* (- d*)))
    (:instance exists-better-suff
               (d? (- (mv-nth 0 (exists-better-witness (- d*) i* f minlen))))
               (i? (mv-nth 1 (exists-better-witness (- d*) i* f minlen)))))))

(define selection-spec
  ((d integerp)
   (i integerp)
   (v real/rationalp)
   (f formatp)
   (minlen posp))
  :returns (yes booleanp :rule-classes ())
  (acl2::b*
   ((d (ifix d))
    (i (ifix i))
    (v (realfix v))
    (f (format-fix f))
    (minlen (acl2::pos-fix minlen)))
  (and (<= minlen (D-length d))
       (= (recover d i f) v)
       (not (exists-better d i f minlen))))
  ///
  (fty::deffixequiv selection-spec :hints (("goal" :in-theory (disable ifix))))
  (acl2::with-arith5-nonlinear-help
   (defruled selection-spec-minus
     (equal (selection-spec d i (- v) f minlen)
            (selection-spec (- d) i v f minlen))
     :use (:instance lemma
                     (d (ifix d))
                     (i (ifix i)))
     :enable minus-ifix
     :prep-lemmas
     ((acl2::with-arith5-help
       (defruled lemma
         (implies (and (integerp d)
                       (integerp i))
                  (equal (selection-spec d i (- v) f minlen)
                         (selection-spec (- d) i v f minlen)))
         :enable exists-better-minus))))))
#|
(rule
 (implies (and (specification d1 i1 v f minlen)
               (specification d2 i2 v f minlen)
               (not (= (realfix v) 0)))

          (equal (D-value d1 i1) (D-value d2 i2)))
 :enable specification
 :disable exists-better
 :prep-lemmas
 ((defrule lemma1
    (implies (and (specification d1 i1 v f minlen)
                  (specification d2 i2 v f minlen))
             (equal (D-length d1) (D-length d2)))
    :enable (specification better)
    :disable (exists-better ifix)
    :cases ((< (D-length d1) (D-length d2))
            (> (D-length d1) (D-length d2)))
    :hints
    (("subgoal 2" :use (:instance exists-better-suff
                                  (d* (ifix d2))
                                  (i* (ifix i2))
                                  (f (format-fix f))
                                  (minlen (acl2::pos-fix minlen))
                                  (d? (ifix d1))
                                  (i? (ifix i1))))
     ("subgoal 1" :use (:instance exists-better-suff
                                  (d* (ifix d1))
                                  (i* (ifix i1))
                                  (f (format-fix f))
                                  (minlen (acl2::pos-fix minlen))
                                  (d? (ifix d2))
                                  (i? (ifix i2))))))

  )
 )
|#
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
