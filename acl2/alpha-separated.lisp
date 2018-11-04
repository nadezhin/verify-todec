(in-package "RTL")
(include-book "fty-lemmas")

(local (acl2::allow-arith5-help))

(defun-sk alpha-separated (alpha maximum a b)
  (forall (x y) (implies (and (natp x)
                              (<= x maximum)
                              (integerp y))
                         (acl2::b*
                          ((alpha*x (* alpha x)))
                          (or (<= y (- alpha*x a))
                              (= y alpha*x)
                              (>= y (+ alpha*x b)))))))
(in-theory (disable alpha-separated))

(defrule alpha-separated-monotone
   (implies (and (alpha-separated alpha maximum1 a1 b1)
                (<= maximum maximum1)
                (<= a a1)
                (<= b b1))
            (alpha-separated alpha maximum a b))
   :use (alpha-separated
         (:instance alpha-separated-necc
                    (maximum maximum1)
                    (a a1)
                    (b b1)
                    (x (mv-nth 0 (alpha-separated-witness alpha maximum a b)))
                    (y (mv-nth 1 (alpha-separated-witness alpha maximum a b))))))

(acl2::with-arith5-help
 (defrule alpha-separated-mod-1
  (implies (alpha-separated (mod alpha 1) maximum a b)
           (alpha-separated alpha maximum a b))
  :rule-classes ()
  :use (alpha-separated
        (:instance alpha-separated-necc
                   (alpha (mod alpha 1))
                   (x (mv-nth 0 (alpha-separated-witness alpha maximum a b)))
                   (y (- (mv-nth 1 (alpha-separated-witness alpha maximum a b))
                         (* (mv-nth 0 (alpha-separated-witness
                                       alpha maximum a b))
                            (floor alpha 1))))))))

(defrule alpha-separated-maxumum=0
  (alpha-separated alpha 0 1 1)
  :use (:instance alpha-separated
                  (maximum 0)
                  (a 1)
                  (b 1)))

(acl2::with-arith5-help
 (defrule alpha-separated-maximum=1
   (implies (real/rationalp alpha)
            (alpha-separated alpha 1 (mod alpha 1) (- 1 (mod alpha 1))))
   :use (:instance alpha-separated
                   (maximum 1)
                   (a (mod alpha 1))
                   (b (- 1 (mod alpha 1))))
   :cases
   ((= (mv-nth 0 (alpha-separated-witness
                  alpha 1 (mod alpha 1) (- 1 (mod alpha 1)))) 0)
    (= (mv-nth 0 (alpha-separated-witness
                  alpha 1 (mod alpha 1) (- 1 (mod alpha 1)))) 1))))

(defrule alpha-separated-integer-alpha
  (implies
   (integerp alpha)
   (alpha-separated alpha maximum 1 1))
  :use (:instance alpha-separated
                  (a 1)
                  (b 1)))

(acl2::with-arith5-help
 (defrule alpha-separated-periodical
   (implies (and (alpha-separated alpha (1- period) a a)
                 (posp period)
                 (natp maximum)
                 (integerp (* alpha period)))
            (alpha-separated alpha maximum a a))
   :cases ((integerp (* alpha period (floor maximum period))))
   :use ((:instance alpha-separated
                    (b a))
         (:instance alpha-separated-necc
                    (maximum (1- period))
                    (b a)
                    (x (mod (mv-nth 0 (alpha-separated-witness alpha maximum a a)) period))
                    (y (- (mv-nth 1 (alpha-separated-witness alpha maximum a a))
                          (* alpha
                             period
                             (floor (mv-nth 0 (alpha-separated-witness
                                               alpha maximum a a))
                                    period))))))
   :prep-lemmas
   ((acl2::with-arith5-help
     (defruled lemma
       (implies (and (integerp (* alpha period))
                     (integerp i))
                (integerp (* alpha period i)))))
    (acl2::with-arith5-help
     (defrule lemma2
       (implies (posp period)
                (equal (+ (* alpha (mod x period))
                          (* alpha period (floor x period)))
                       (* alpha x))))))))

(defruled alpha-spearated-before-periodic
  (implies (and (alpha-separated alpha (+ -1 nu s) a a)
               (real/rationalp alpha)
               (real/rationalp a)
               (posp s)
               (posp nu)
               (integerp maximum)
               (< 0 a)
               (integerp (+ (- a) (* alpha s)))
               (integerp (+ a (* alpha nu))))
          (alpha-separated alpha maximum a a))
  :use (:instance alpha-separated-periodical
                  (period (+ nu s)))
  :prep-lemmas
  ((acl2::with-arith5-nonlinear++-help
    (defrule lemma
      (implies (and (integerp (+ (- a) (* alpha s)))
                    (integerp (+ a (* alpha nu))))
               (integerp (+ (* alpha nu) (* alpha s))))
      :use (:instance lemma0
                      (x (+ (- a) (* alpha s)))
                      (y (+ a (* alpha nu))))
      :prep-lemmas
      ((defrule lemma0
         (implies (and (integerp x) (integerp y))
                  (integerp (+ x y)))))))))

(acl2::with-arith5-help
 (defrule alpha-separated-decrease-a
   (implies (and (alpha-separated alpha maximum1 a+b b)
                 (real/rationalp alpha)
                 (real/rationalp a)
                 (real/rationalp b)
                 (integerp maximum)
                 (integerp maximum1)
                 (<= maximum1 maximum)
                 (<= maximum (1+ (* 2 maximum1)))
                 (<= 0 b)
                 (= a+b (+ a b))
                 (integerp (+ (* alpha (- maximum maximum1)) b)))
            (alpha-separated alpha maximum a b))
   :use alpha-separated
   :cases ((> (mv-nth 0 (alpha-separated-witness alpha maximum a b))
            maximum1))
   :hints
   (("subgoal 2" :use
     (:instance alpha-separated-necc
                (maximum maximum1)
                (a a+b)
                (x (mv-nth 0 (alpha-separated-witness alpha maximum a b)))
                (y (mv-nth 1 (alpha-separated-witness alpha maximum a b)))))
    ("subgoal 1" :use
     (:instance alpha-separated-necc
                (maximum maximum1)
                (a a+b)
                (x (- (mv-nth 0 (alpha-separated-witness alpha maximum a b))
                      (- maximum maximum1)))
                (y (- (mv-nth 1 (alpha-separated-witness alpha maximum a b))
                      (+ (* alpha (- maximum maximum1)) b))))))))

(acl2::with-arith5-nonlinear-help
 (defrule alpha-separated-decrease-b
   (implies (and (alpha-separated alpha maximum1 a a+b)
                 (real/rationalp alpha)
                 (real/rationalp a)
                 (real/rationalp b)
                 (integerp maximum)
                 (integerp maximum1)
                 (<= maximum1 maximum)
                 (<= maximum (1+ (* 2 maximum1)))
                 (<= 0 a)
                 (= a+b (+ a b))
                 (integerp (- (* alpha (- maximum maximum1)) a)))
            (alpha-separated alpha maximum a b))
   :use alpha-separated
   :cases ((> (mv-nth 0 (alpha-separated-witness alpha maximum a b)) maximum1))
   :hints
   (("subgoal 2" :use
     (:instance alpha-separated-necc
                (maximum maximum1)
                (b a+b)
                (x (mv-nth 0 (alpha-separated-witness alpha maximum a b)))
                (y (mv-nth 1 (alpha-separated-witness alpha maximum a b)))))
    ("subgoal 1" :use
     (:instance alpha-separated-necc
                (maximum maximum1)
                (b a+b)
                (x (- (mv-nth 0 (alpha-separated-witness alpha maximum a b))
                      (- maximum maximum1)))
                (y (- (mv-nth 1 (alpha-separated-witness alpha maximum a b))
                      (- (* alpha (- maximum maximum1)) a))))))))

(define alpha-separated-real-search-aux
  ((maximum posp)
   (a real/rationalp)
   (b real/rationalp)
   (s posp)
   (nu posp))
  :measure (nfix (- (acl2::pos-fix maximum)
                    (max (acl2::pos-fix s) (acl2::pos-fix nu))))
  :returns (mv (a real/rationalp :rule-classes :type-prescription
                  :hints (("goal" :in-theory (disable realfix))))
               (b real/rationalp :rule-classes :type-prescription
                  :hints (("goal" :in-theory (disable realfix))))
               (s posp :rule-classes :type-prescription
                  :hints (("goal" :in-theory (disable realfix))))
               (nu posp :rule-classes :type-prescription
                  :hints (("goal" :in-theory (disable realfix)))))
  (acl2::b*
   ((maximum (acl2::pos-fix maximum))
    (a (realfix a))
    (b (realfix b))
    (s (acl2::pos-fix s))
    (nu (acl2::pos-fix nu))
    (s+nu (+ s nu))
    (s+nu<=maximum (<= s+nu maximum))
    (a-b (- a b)))
   (cond
    ((and s+nu<=maximum (< a-b 0))
     (alpha-separated-real-search-aux maximum a (- a-b) s s+nu))
    ((and s+nu<=maximum (< 0 a-b))
     (alpha-separated-real-search-aux maximum a-b b s+nu nu))
    (t (mv a b s nu))))
  ///
  (fty::deffixequiv alpha-separated-real-search-aux)
  (acl2::with-arith5-help
   (defrule alpha-separated-real-search-aux-correct
     (acl2::b*
      (((mv ret-a ret-b ?ret-s ?ret-nu)
        (alpha-separated-real-search-aux maximum a b s nu)))
      (implies
       (and (real/rationalp alpha)
            (real/rationalp a)
            (real/rationalp b)
            (posp s)
            (posp nu)
            (posp maximum)
            (< 0 a)
            (< 0 b)
            (integerp (- (* alpha s) a))
            (integerp (+ (* alpha nu) b))
            (alpha-separated alpha (+ -1 s nu) a b))
       (alpha-separated alpha maximum ret-a ret-b)))
     :enable alpha-spearated-before-periodic)))

(define alpha-separated-int-search-aux
  ((maximum posp)
   (a posp)
   (b posp)
   (s posp)
   (nu posp))
  :measure (nfix (- (acl2::pos-fix maximum)
                    (max (acl2::pos-fix s) (acl2::pos-fix nu))))
  :returns (mv (a posp :rule-classes :type-prescription)
               (b posp :rule-classes :type-prescription)
               (s posp :rule-classes :type-prescription)
               (nu posp :rule-classes :type-prescription))
  (acl2::b*
   ((maximum (acl2::pos-fix maximum))
    (a (acl2::pos-fix a))
    (b (acl2::pos-fix b))
    (s (acl2::pos-fix s))
    (nu (acl2::pos-fix nu))
    (s+nu (+ s nu))
    (s+nu<=maximum (<= s+nu maximum))
    (a-b (- a b)))
   (cond
    ((and s+nu<=maximum (< a-b 0))
     (alpha-separated-int-search-aux maximum a (- a-b) s s+nu))
    ((and s+nu<=maximum (< 0 a-b))
     (alpha-separated-int-search-aux maximum a-b b s+nu nu))
    (t (mv a b s nu))))
  ///
  (fty::deffixequiv alpha-separated-int-search-aux)
  (acl2::with-arith5-help
   (defruled alpha-separated-int-search-aux-as-real
     (acl2::b*
      ((a (/ (acl2::pos-fix ai) modulus))
       (b (/ (acl2::pos-fix bi) modulus))
       ((mv a-real b-real) (alpha-separated-real-search-aux maxumum a b s nu))
       ((mv a-int b-int) (alpha-separated-int-search-aux maxumum ai bi s nu)))
      (implies
       (posp modulus)
       (and
        (equal a-int (* a-real modulus))
        (equal b-int (* b-real modulus)))))
     :enable alpha-separated-real-search-aux
     :induct (alpha-separated-int-search-aux maxumum ai bi s nu))))

(define alpha-separated-real-search
  ((maximum natp)
   (alpha real/rationalp))
  :returns (mv (a real/rationalp :rule-classes :type-prescription)
               (b real/rationalp :rule-classes :type-prescription))
  (acl2::b*
   ((alpha (realfix alpha))
    (a (mod alpha 1))
    ((when (or (zp maximum) (= a 0))) (mv 1 1))
    (b (- 1 a))
    ((mv a b ?s ?nu)
     (alpha-separated-real-search-aux maximum a b 1 1)))
   (mv a b))
  ///
  (acl2::with-arith5-help
   (fty::deffixequiv alpha-separated-real-search))
  (acl2::with-arith5-help
   (defrule alpha-separated-real-search-correct
     (acl2::b*
      (((mv ret-a ret-b) (alpha-separated-real-search maximum alpha)))
      (implies
       (and (real/rationalp alpha)
            (natp maximum))
       (alpha-separated alpha maximum ret-a ret-b)))
     :use (:instance alpha-separated-real-search-aux-correct
                     (a (mod alpha 1))
                     (b (- 1 (mod alpha 1)))
                     (s 1)
                     (nu 1)))))

(acl2::with-arith5-help
 (define alpha-separated-int-search
   ((maximum natp)
    (multiplier integerp)
    (modulus posp))
   :returns (mv (a posp :rule-classes :type-prescription)
                (b posp :rule-classes :type-prescription))
   (acl2::b*
    ((multiplier (ifix multiplier))
     (modulus (acl2::pos-fix modulus))
     (a (mod multiplier modulus))
     ((when (or (zp maximum) (= a 0))) (mv modulus modulus))
     (b (- modulus a))
     ((mv a b ?s ?nu)
      (alpha-separated-int-search-aux maximum a b 1 1)))
    (mv a b))
   ///
   (fty::deffixequiv alpha-separated-int-search)
   (defruled alpha-separated-int-search-as-real
     (acl2::b*
      ((alpha (/ (ifix multiplier) (acl2::pos-fix modulus)))
       ((mv a-real b-real) (alpha-separated-real-search maxumum alpha))
       ((mv a-int b-int)
        (alpha-separated-int-search maxumum multiplier modulus)))
      (and
       (equal a-int (* a-real (acl2::pos-fix modulus)))
       (equal b-int (* b-real (acl2::pos-fix modulus)))))
     :enable (alpha-separated-real-search acl2::pos-fix)
     :use (:instance alpha-separated-int-search-aux-as-real
                     (ai (mod (ifix multiplier) (acl2::pos-fix modulus)))
                     (bi (- (acl2::pos-fix modulus)
                            (mod (ifix multiplier) (acl2::pos-fix modulus))))
                     (s 1)
                     (nu 1)))))

(acl2::with-arith5-help
 (define alpha-separated-rat-search
  ((maximum natp)
   (alpha rationalp))
   :returns (mv (a pos-rationalp :rule-classes :type-prescription)
                (b pos-rationalp :rule-classes :type-prescription))
   (acl2::b*
    ((alpha (rfix alpha))
     (multiplier (numerator alpha))
     (modulus (denominator alpha))
     ((mv a b) (alpha-separated-int-search maximum multiplier modulus)))
    (mv (/ a modulus) (/ b modulus)))
   ///
   (fty::deffixequiv alpha-separated-rat-search
                     :hints (("goal" :in-theory (disable nfix))))
   (defruled alpha-separated-rat-search-as-real
     (acl2::b*
      (((mv a-real b-real) (alpha-separated-real-search maximum (rfix alpha)))
       ((mv a-rat b-rat)
        (alpha-separated-rat-search maximum alpha)))
      (and
       (equal a-rat a-real)
       (equal b-rat b-real)))
     :enable alpha-separated-int-search-as-real)))

(defrule alpha-separated-rat-search-correct
  (acl2::b*
   (((mv ret-a ret-b) (alpha-separated-rat-search maximum alpha)))
   (implies
    (and (rationalp alpha)
         (natp maximum))
    (alpha-separated alpha maximum ret-a ret-b)))
  :enable alpha-separated-rat-search-as-real)
