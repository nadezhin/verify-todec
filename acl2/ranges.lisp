(in-package "RTL")
(include-book "std/util/defconsts" :dir :system)
(include-book "section3")

(local (include-book "rtl/rel11/support/float" :dir :system))
(local (acl2::allow-arith5-help))

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

(fty::defprod fp-range
   ((f formatp)
    (q integerp)
    (c-min posp)
    (c-max posp)
    (ord2 integerp)
    (ordD integerp)
    (qb integerp)))

(acl2::with-arith5-help
 (define valid-fp-range-p
   ((range fp-range-p))
   :returns (yes booleanp :rule-classes ())
   (let* ((f (fp-range->f range))
          (q (fp-range->q range))
          (c-min (fp-range->c-min range))
          (c-max (fp-range->c-max range))
          (ord2 (fp-range->ord2 range))
          (ordD (fp-range->ordD range))
          (qb (fp-range->qb range))
          (v-min (* c-min (expt 2 q)))
          (v-max (* c-max (expt 2 q))))
     (and (<= (Qmin f) q)
          (<= q (Qmax f))
          (or (= q (Qmin f)) (<= (2^{P-1} f) c-min))
          (<= c-min c-max)
          (<= c-max (Cmax f))
          (= (ord2 v-min) ord2)
          (= (ord2 v-max) ord2)
          (= (ordD v-min) ordD)
          (= (ordD v-max) ordD)
          (= (qb v-min f) qb)
          (= (qb v-max f) qb)))
   ///
   (fty::deffixequiv valid-fp-range-p)))

;; fp-range

(acl2::with-arith5-help
 (defruled valid-fp-range-necc
   (implies (and (valid-fp-range-p range)
                 (integerp c)
                 (<= (fp-range->c-min range) c)
                 (<= c (fp-range->c-max range)))
            (let ((f (fp-range->f range))
                  (v (* c (expt 2 (fp-range->q range)))))
              (and (finite-positive-binary-p v f)
                   (= (q v f) (fp-range->q range))
                   (= (c v f) c)
                   (= (ord2 v) (fp-range->ord2 range))
                   (= (ordD v) (fp-range->ordD range))
                   (= (qb v f) (fp-range->qb range)))))
   :enable valid-fp-range-p
   :hints
   (("subgoal 12" :in-theory (enable Cmax) :use
     (:instance finite-positive-binary-suff
                (f (fp-range->f range))
                (q (fp-range->q range))))
    ("subgoal 11" :in-theory (enable result-1-5) :use
     ((:instance result-1-4
                 (x (* (fp-range->c-min range) (expt 2 (fp-range->q range))))
                 (y (* c (expt 2 (fp-range->q range)))))
      (:instance result-1-4
                 (x (* c (expt 2 (fp-range->q range))))
                 (y (* (fp-range->c-max range) (expt 2 (fp-range->q range)))))))
    ("subgoal 10" :in-theory (enable CMax) :use
     (:instance unique-c*2^q
                (f (fp-range->f range))
                (q (fp-range->q range))))
    ("subgoal 9" :in-theory (enable CMax) :use
     (:instance unique-c*2^q
                (f (fp-range->f range))
                (q (fp-range->q range))))
    ("subgoal 8" :use
     ((:instance qb-monotone
                 (f (fp-range->f range))
                 (v1 (* (fp-range->c-min range) (expt 2 (fp-range->q range))))
                 (v2 (* c (expt 2 (fp-range->q range)))))
      (:instance qb-monotone
                 (f (fp-range->f range))
                 (v1 (* c (expt 2 (fp-range->q range))))
                 (v2 (* (fp-range->c-max range) (expt 2 (fp-range->q range)))))))
    ("subgoal 7" :in-theory (enable ord2) :use
     ((:instance expe-monotone
                 (b 2)
                 (x (* (fp-range->c-min range) (expt 2 (fp-range->q range))))
                 (y (* c (expt 2 (fp-range->q range)))))
      (:instance expe-monotone
                 (b 2)
                 (x (* c (expt 2 (fp-range->q range))))
                 (y (* (fp-range->c-max range) (expt 2 (fp-range->q range)))))))
    ("subgoal 6" :in-theory (enable Cmax) :use
     (:instance finite-positive-binary-suff
                (f (fp-range->f range))
                (q (fp-range->q range))))
    ("subgoal 5" :in-theory (enable result-1-5) :use
     ((:instance result-1-4
                 (x (* (fp-range->c-min range) (expt 2 (fp-range->q range))))
                 (y (* c (expt 2 (fp-range->q range)))))
      (:instance result-1-4
                 (x (* c (expt 2 (fp-range->q range))))
                 (y (* (fp-range->c-max range) (expt 2 (fp-range->q range)))))))
    ("subgoal 4" :in-theory (enable CMax) :use
     (:instance unique-c*2^q
                (f (fp-range->f range))
                (q (fp-range->q range))))
    ("subgoal 3" :in-theory (enable CMax) :use
     (:instance unique-c*2^q
                (f (fp-range->f range))
                (q (fp-range->q range))))
    ("subgoal 2" :use
     ((:instance qb-monotone
                 (f (fp-range->f range))
                 (v1 (* (fp-range->c-min range) (expt 2 (fp-range->q range))))
                 (v2 (* c (expt 2 (fp-range->q range)))))
      (:instance qb-monotone
                 (f (fp-range->f range))
                 (v1 (* c (expt 2 (fp-range->q range))))
                 (v2 (* (fp-range->c-max range) (expt 2 (fp-range->q range)))))))
    ("subgoal 1" :in-theory (enable ord2) :use
     ((:instance expe-monotone
                 (b 2)
                 (x (* (fp-range->c-min range) (expt 2 (fp-range->q range))))
                 (y (* c (expt 2 (fp-range->q range)))))
      (:instance expe-monotone
                 (b 2)
                 (x (* c (expt 2 (fp-range->q range))))
                 (y (* (fp-range->c-max range)
                       (expt 2 (fp-range->q range))))))))))

(acl2::with-arith5-help
 (defruled valid-fp-range-necc-alt
   (implies (and (valid-fp-range-p range)
                 (equal f (fp-range->f range))
                 (finite-positive-binary-p (pos-rational-fix v) f)
                 (= (q v f) (fp-range->q range))
                 (<= (fp-range->c-min range) (c v f))
                 (<= (c v f) (fp-range->c-max range)))
            (and (= (ord2 v) (fp-range->ord2 range))
                 (= (ordD v) (fp-range->ordD range))
                 (= (qb v f) (fp-range->qb range))))
   :cases ((= (pos-rational-fix v) (* (c v f) (expt 2 (q v f)))))
   :hints (("subgoal 2" :use (:instance finite-positive-binary-necc
                                        (x (pos-rational-fix v))))
           ("subgoal 1" :use (:instance valid-fp-range-necc
                                        (c (c v f)))))))

(fty::deflist fp-range-list :elt-type fp-range :true-listp t)

(define valid-fp-ranges-p
  ((ranges fp-range-list-p)
   (f formatp))
  :returns (yes booleanp :rule-classes ())
  (or (atom ranges)
      (and (consp ranges)
           (valid-fp-range-p (car ranges))
           (equal (fp-range->f (car ranges)) (format-fix f))
           (valid-fp-ranges-p (cdr ranges) f)
           (if (atom (cdr ranges))
               (and (= (fp-range->q (car ranges)) (Qmin f))
                    (= (fp-range->c-min (car ranges)) 1))
             (or (and (= (fp-range->q (car ranges))
                         (fp-range->q (cadr ranges)))
                      (= (fp-range->c-min (car ranges))
                         (1+ (fp-range->c-max (cadr ranges)))))
                 (and (> (fp-range->q (car ranges)) (Qmin f))
                      (= (fp-range->q (car ranges))
                         (1+ (fp-range->q (cadr ranges))))
                      (= (fp-range->c-min (car ranges)) (2^{P-1} f))
                      (= (fp-range->c-max (cadr ranges)) (CMax f)))))))
  ///
  (fty::deffixequiv valid-fp-ranges-p))

(acl2::with-arith5-help
 (define gen-fp-range
   ((f formatp)
    (q integerp)
    (c-min posp)
    (c-max posp))
   :returns (range fp-range-p)
   (let ((v (* (acl2::pos-fix c-min) (expt 2 (ifix q)))))
     (make-fp-range
      :f f
      :q q
      :c-min c-min
      :c-max c-max
      :ord2 (ord2 v)
      :ordD (ordD v)
      :qb (qb v f)))
   ///
   (fty::deffixequiv gen-fp-range)))

(acl2::with-arith5-help
 (define gen-fp-subnormals
   ((p natp)
    (f formatp))
  :returns (ranges fp-range-list-p)
  (and (posp p)
       (let* ((MIN_VALUE (MIN_VALUE f))
              (c-min (expt 2 (1- p)))
              (c-max (1- (expt 2 p)))
              (ordD (ordD (* c-min MIN_VALUE)))
              (v-mid (expt (D) ordD))
              (c-mid (cg (/ v-mid MIN_VALUE))))
         (if (or (> c-mid c-max)
                 (<= c-mid c-min))
           (list*
            (gen-fp-range f (Qmin f) c-min c-max)
            (gen-fp-subnormals (1- p) f))
           (list*
            (gen-fp-range f (Qmin f) c-mid c-max)
            (gen-fp-range f (Qmin f) c-min (1- c-mid))
            (gen-fp-subnormals (1- p) f)))))
  ///
  (fty::deffixequiv gen-fp-subnormals)))

(acl2::with-arith5-help
 (define gen-fp-ranges
   ((q integerp)
    (f formatp))
   :measure (nfix (- (ifix q) (Qmin f)))
   :returns (ranges fp-range-list-p)
   (let ((q (ifix q)))
     (if (<= q (Qmin f))
         (gen-fp-subnormals (P f) f)
       (let* ((c-min (2^{P-1} f))
              (c-max (Cmax f))
              (ordD (ordD (* c-min (expt 2 q))))
              (v-mid (expt (D) ordD))
              (c-mid (max 2 (cg (* v-mid (expt 2 (- q)))))))
         (if (or (> c-mid c-max)
                 (= c-mid (1+ c-min)))
             (list*
              (gen-fp-range f q (1+ c-min) c-max)
              (gen-fp-range f q c-min c-min)
              (gen-fp-ranges (1- q) f))
           (list*
            (gen-fp-range f q c-mid c-max)
            (gen-fp-range f q (1+ c-min) (1- c-mid))
            (gen-fp-range f q c-min c-min)
            (gen-fp-ranges (1- q) f))))))
   ///
   (fty::deffixequiv gen-fp-ranges)))

(defconsts *ranges-hp*
  (let ((f (hp)))
    (gen-fp-ranges (Qmax f) f)))

(define ranges-hp
  ()
  :returns (ranges (valid-fp-ranges-p ranges (hp))
                   :hints (("goal" :in-theory (enable (hp)))))
  *ranges-hp*
  ///
  (defrule ranges-hp-full
    (and (equal (fp-range->q (car (ranges-hp))) (Qmax (hp)))
         (equal (fp-range->c-max (car (ranges-hp))) (Cmax (hp))))
    :enable ((hp)))
  (in-theory (disable (ranges-hp))))

(defconsts *ranges-sp*
  (let ((f (sp)))
    (gen-fp-ranges (Qmax f) f)))

(define ranges-sp
  ()
  :returns (ranges (valid-fp-ranges-p ranges (sp))
                   :hints (("goal" :in-theory (enable (sp)))))
  *ranges-sp*
  ///
  (defrule ranges-sp-full
    (and (equal (fp-range->q (car (ranges-sp))) (Qmax (sp)))
         (equal (fp-range->c-max (car (ranges-sp))) (Cmax (sp))))
    :enable ((sp)))
  (in-theory (disable (ranges-sp))))

(defconsts *ranges-dp*
  (let ((f (dp)))
    (gen-fp-ranges (Qmax f) f)))

(define ranges-dp
  ()
  :returns (ranges (valid-fp-ranges-p ranges (dp))
                   :hints (("goal" :in-theory (enable (dp)))))
  *ranges-dp*
  ///
  (defrule ranges-dp-full
    (and (equal (fp-range->q (car (ranges-dp))) (Qmax (dp)))
         (equal (fp-range->c-max (car (ranges-dp))) (Cmax (dp))))
    :enable ((dp)))
  (in-theory (disable (ranges-dp))))

(encapsulate
  (((Pred * *) => *)
   ((check-Pred-on-range * * * * * * *) => *))

  (local (defun Pred (v f)
           (declare (ignore v f))
           t))

  (local (defun check-Pred-on-range (f q c-min c-max ord2 ordD qb)
           (declare (ignore f q c-min c-max ord2 ordD qb))
           t))

  (defruled check-Pred-on-range-correct
    (implies (and (finite-positive-binary-p v f)
                  (check-Pred-on-range
                   f
                   (q v f)
                   c-min c-max
                   (ord2 v)
                   (ordD v)
                   (qb v f))
                  (posp c-min)
                  (posp c-max)
                  (or (= (q v f) (Qmin f)) (<= (2^{P-1} f) c-min))
                  (<= c-min (c v f))
                  (<= (c v f) c-max)
                  (<= c-max (Cmax f)))
             (Pred v f))))

(define check-Pred-on-ranges
  ((ranges fp-range-list-p))
  :returns (yes booleanp :rule-classes ())
  (or (atom ranges)
      (and (check-Pred-on-range
            (fp-range->f (car ranges))
            (fp-range->q (car ranges))
            (fp-range->c-min (car ranges))
            (fp-range->c-max (car ranges))
            (fp-range->ord2 (car ranges))
            (fp-range->ordD (car ranges))
            (fp-range->qb (car ranges)))
           (check-Pred-on-ranges (cdr ranges))))
  ///
  (fty::deffixequiv check-Pred-on-ranges)
  (acl2::with-arith5-help
   (defrule check-Pred-on-ranges-correct
     (implies (and (valid-fp-ranges-p ranges f)
                   (check-Pred-on-ranges ranges)
                   (finite-positive-binary-p v f)
                   (consp ranges)
                   (or (< (q v f) (fp-range->q (car ranges)))
                       (and (= (q v f) (fp-range->q (car ranges)))
                            (<= (c v f) (fp-range->c-max (car ranges))))))
              (Pred v f))
     :enable (valid-fp-ranges-p)
     :induct (check-Pred-on-ranges ranges)
     :hints
     (("subgoal *1/1" :do-not-induct t :cases
       ((and (= (q v f) (fp-range->q (car ranges)))
             (>= (c v f) (fp-range->c-min (car ranges))))))
      ("subgoal *1/1.2" :cases ((consp (cdr ranges))))
      ("subgoal *1/1.2.2.1" :use (:instance finite-positive-binary-necc
                                            (x v)))
      ("subgoal *1/1.2.1" :cases
       ((and (= (fp-range->q (car ranges))
                (fp-range->q (cadr ranges)))
             (= (fp-range->c-min (car ranges))
                (1+ (fp-range->c-max (cadr ranges)))))
        (and (> (fp-range->q (car ranges)) (Qmin f))
             (= (fp-range->q (car ranges))
                (1+ (fp-range->q (cadr ranges))))
             (= (fp-range->c-min (car ranges)) (2^{P-1} f))
             (= (fp-range->c-max (cadr ranges)) (CMax f))))
       :use (:instance finite-positive-binary-necc
                       (x v)))
      ("subgoal *1/1.1" :in-theory (enable valid-fp-range-p) :use
       ((:instance check-Pred-on-range-correct
                   (f (fp-range->f (car ranges)))
                   (c-min (fp-range->c-min (car ranges)))
                   (c-max (fp-range->c-max (car ranges))))
        (:instance valid-fp-range-necc-alt
                   (range (car ranges)))))))))

