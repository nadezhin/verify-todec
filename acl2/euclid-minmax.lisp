(in-package "RTL")
;(include-book "ihs/basic-definitions" :dir :system)
;(include-book "kestrel/utilities/fixbytes/instances" :dir :system)
;(include-book "rtl/rel11/support/definitions" :dir :system)
(include-book "cont-fractions")

;(include-book "tools/with-arith5-help" :dir :system)
(local (acl2::allow-arith5-help))

(local (include-book "rtl/rel11/support/basic" :dir :system))

; info.adams.ryu.analysis.EuclidMinMax.min

(define EuclidMinMax-min-loop
  ((maximum integerp)
   (modulo integerp)
   (a integerp)
   (b integerp)
   (c integerp)
   (s integerp)
   (t_ integerp)
   (u integerp)
   (v integerp)
   (beforeLoopA booleanp))
  :measure (+ (nfix a) (nfix b))
  :returns (mv (min integerp :hyp (integerp c))
               (max integerp :hyp (and (integerp c) (integerp modulo))))
  (cond
   ((or (not (posp a)) (not (posp b))) (mv 0 0))
   ((or (and beforeLoopA (>= b a))
        (and (not beforeLoopA) (< a b) (not (= a 0))))
    (acl2::b*
     ((b-new (- b a))
      (u-new (- u s))
      (v-new (- v t_)))
     (if (>= (- u-new) maximum)
         (mv (* a c)
             (- modulo
                (* (if (> (- u-new) maximum) b b-new) c)))
       (EuclidMinMax-min-loop
        maximum modulo a b-new c s t_ u-new v-new t))))
   ((or (and beforeLoopA (< b a) (not (= b 0)))
        (and (not beforeLoopA) (>= a b)))
    (acl2::b*
     ((a-new (- a b))
      (s-new (- s u))
      (t-new (- t_ v)))
     (if (>= s-new maximum)
         (mv (* (if (> s-new maximum) a a-new) c)
             (- modulo (* b c)))
       (EuclidMinMax-min-loop
        maximum modulo a-new b c s-new t-new u v nil))))
   (t (mv 0 (- modulo c)))))

(define EuclidMinMax-min
  ((multiplier integerp)
   (modulo integerp)
   (maximum integerp))
  :returns (mv (min integerp)
               (max integerp :hyp (integerp modulo)))
  (let ((a multiplier)
        (b modulo)
        (c 1))
    (if (>= maximum b)
        (mv 0 (- modulo c))
      (EuclidMinMax-min-loop
       maximum modulo a b c 1 0 0 1 t))))

; info.adams.ryu.analysis.EuclidMinMax.max

(acl2::with-arith5-help
 (define EuclidMinMax-max-loop
  ((maximum integerp)
   (modulo integerp)
   (a integerp)
   (b integerp)
   (c integerp)
   (s integerp)
   (t_ integerp)
   (u integerp)
   (v integerp)
   (beforeLoopA booleanp))
  :measure (+ (nfix a) (nfix b))
;  :returns (mv (min integerp :hyp (integerp c))
;               (max integerp :hyp (and (integerp c) (integerp modulo))))
  (cond
   ((or (not (posp a)) (not (posp b)) (not (posp s))) (mv 0 0))
   ((or (and beforeLoopA (>= b a))
        (and (not beforeLoopA) (> b a) (not (= a 0))))
    (acl2::b*
     ((q (floor b a))
      (q (min q (- (floor (- maximum (- u)) s) 1)))
      (q (max q 1))
      (b-new (- b (* a q)))
      (u-new (- u (* s q)))
      (v-new (- v (* t_ q))))
     (if (>= (- u-new) maximum)
         (mv (* a c)
             (- modulo
                (* (if (> (- u-new) maximum) b b-new) c)))
       (EuclidMinMax-max-loop
        maximum modulo a b-new c s t_ u-new v-new t))))
   ((or (and beforeLoopA (< b a) (not (= b 0)))
        (and (not beforeLoopA) (<= b a)))
    (acl2::b*
     ((q 1)
      (q (if (= u 1)
             q
           (min q (/ (- maximum s) (+ (- u) 1)))))
      (q (max q 1))
      (a-new (- a (* b q)))
      (s-new (- s (* u q)))
      (t-new (- t_ (* v q))))
     (if (>= s-new maximum)
         (mv (* (if (> s-new maximum) a a-new) c)
             (- modulo (* b c)))
       (EuclidMinMax-max-loop
        maximum modulo a-new b c s-new t-new u v nil))))
   (t (mv 0 (- modulo c))))))

(define EuclidMinMax-max
  ((multiplier integerp)
   (modulo integerp)
   (maximum integerp))
;  :returns (mv (min integerp)
;               (max integerp :hyp (integerp modulo)))
  (let ((a multiplier)
        (b modulo)
        (c 1))
    (if (>= maximum b)
        (mv 0 (- modulo c))
      (EuclidMinMax-max-loop
       maximum modulo a b c 1 0 0 1 t))))

#|
(EuclidMinMax-min 10 33 0) ; (10 0)
(EuclidMinMax-min 10 33 1) ; (10 10)
(EuclidMinMax-min 10 33 2) ; (10 20)
(EuclidMinMax-min 10 33 3) ; (10 30)
(EuclidMinMax-min 10 33 4) ; (7 30)
(EuclidMinMax-min 10 33 5) ; (7 30)
(EuclidMinMax-min 10 33 6) ; (7 30)
(EuclidMinMax-min 10 33 7) ; (4 30)
(EuclidMinMax-min 10 33 8) ; (4 30)
(EuclidMinMax-min 10 33 9) ; (4 30)
(EuclidMinMax-min 10 33 10) ; (1 30)
(EuclidMinMax-min 10 33 11) ; (1 30)
(EuclidMinMax-min 10 33 12) ; (1 30)
(EuclidMinMax-min 10 33 13) ; (1 31)
(EuclidMinMax-min 10 33 14) ; (1 31)
(EuclidMinMax-min 10 33 15) ; (1 31)
(EuclidMinMax-min 10 33 16) ; (1 31)
(EuclidMinMax-min 10 33 17) ; (1 31)
(EuclidMinMax-min 10 33 18) ; (1 31)
(EuclidMinMax-min 10 33 19) ; (1 31)
(EuclidMinMax-min 10 33 20) ; (1 31)
(EuclidMinMax-min 10 33 21) ; (1 31)
(EuclidMinMax-min 10 33 22) ; (1 31)
(EuclidMinMax-min 10 33 23) ; (1 32)
(EuclidMinMax-min 10 33 24) ; (1 32)
(EuclidMinMax-min 10 33 25) ; (1 32)
(EuclidMinMax-min 10 33 26) ; (1 32)
(EuclidMinMax-min 10 33 27) ; (1 32)
(EuclidMinMax-min 10 33 28) ; (1 32)
(EuclidMinMax-min 10 33 29) ; (1 32)
(EuclidMinMax-min 10 33 30) ; (1 32)
(EuclidMinMax-min 10 33 31) ; (1 32)
(EuclidMinMax-min 10 33 32) ; (1 32)
(EuclidMinMax-min 10 33 33) ; (0 32)

(EuclidMinMax-max 10 33 0) ; (10 0)
(EuclidMinMax-max 10 33 1) ; (10 10)
(EuclidMinMax-max 10 33 2) ; (10 20)
(EuclidMinMax-max 10 33 3) ; (10 30)
(EuclidMinMax-max 10 33 4) ; (7 30)
(EuclidMinMax-max 10 33 5) ; (7 30)
(EuclidMinMax-max 10 33 6) ; (7 30)
(EuclidMinMax-max 10 33 7) ; (4 30)
(EuclidMinMax-max 10 33 8) ; (4 30)
(EuclidMinMax-max 10 33 9) ; (4 30)
(EuclidMinMax-max 10 33 10) ; (1 30)
(EuclidMinMax-max 10 33 11) ; (1 30)
(EuclidMinMax-max 10 33 12) ; (1 30)
(EuclidMinMax-max 10 33 13) ; (1 31)
(EuclidMinMax-max 10 33 14) ; (1 31)
(EuclidMinMax-max 10 33 15) ; (1 31)
(EuclidMinMax-max 10 33 16) ; (1 31)
(EuclidMinMax-max 10 33 17) ; (1 31)
(EuclidMinMax-max 10 33 18) ; (1 31)
(EuclidMinMax-max 10 33 19) ; (1 31)
(EuclidMinMax-max 10 33 20) ; (1 31)
(EuclidMinMax-max 10 33 21) ; (1 31)
(EuclidMinMax-max 10 33 22) ; (1 31)
(EuclidMinMax-max 10 33 23) ; (1 32)
(EuclidMinMax-max 10 33 24) ; (1 32)
(EuclidMinMax-max 10 33 25) ; (1 32)
(EuclidMinMax-max 10 33 26) ; (1 32)
(EuclidMinMax-max 10 33 27) ; (1 32)
(EuclidMinMax-max 10 33 28) ; (1 32)
(EuclidMinMax-max 10 33 29) ; (1 32)
(EuclidMinMax-max 10 33 30) ; (1 32)
(EuclidMinMax-max 10 33 31) ; (1 32)
(EuclidMinMax-max 10 33 32) ; (1 32)
(EuclidMinMax-max 10 33 33) ; (0 32)
|#

(define aaa-aux
  ((maximum natp)
   (i natp)
   (a posp)
   (b posp)
   (s posp)
   (nu natp))
  :measure (+ (nfix a) (nfix b))
  :returns (mv i
               (a posp :rule-classes :type-prescription :hyp (posp a))
               (b posp :rule-classes :type-prescription :hyp (posp b))
               s
               nu)
  (if (and (posp a) (posp b) (not (= a b)) (<= (+ s nu) maximum))
      (if (> b a)
          (aaa-aux maximum (1+ i) a (- b a) s (+ s nu))
       (aaa-aux maximum (1+ i) (- a b) b (+ s nu) nu))
    (mv i a b s nu)))


; (initially a=a0 b=b0 s=1 nu=0)
; if maximum<1 return (a0,b0)
; if a0=0 return (0,b0)
; if a0=n*b0 return (b0,b0)
; if a0=n*b0+a1 0<a1<b0 next step a=a1 b=b0 s=1 nu=0
; next step a=a1 b=b0-a1 s=1 nu=1
; if maximum<2 return (a1,b0-a1)
; if a1=b0/2 return (b0/2,b0/2)
; if a1<b0/2 next step a=a1 b=b0-2*a1 s=1 nu=2 (forall 0<d<2 a/b0<=frac(alpha*d)<=(b0-b-a)/b0)
; if a1>b0/2 next stepp a=2*a1-b0 b=b0-a1 s=2 nu=1 (forall 0<d<2 (a+b)/b0<=frac(alpha*d)<=(b0-b)/b0)

(defund aaa-invariant0 (multiplier modulo maximum a b s nu)
  (acl2::b*
   ((alpha (/ multiplier modulo)))
   (and
    (natp multiplier)
    (posp modulo)
    (natp maximum)
    (posp a)
    (posp b)
    (posp s)
    (natp nu)
    (if (posp nu)
        (and (<= (+ a b) modulo)
             (= (frac-alpha-d alpha s) (/ a modulo)))
      (and (= s 1)
           (= (frac-alpha-d alpha s) (frac (/ a modulo)))))
    (= (frac-alpha-d alpha nu) (- 1 (/ b modulo)))
    (implies
     (<= s nu)
     (frac-alpha-d-in alpha nu (/ a modulo) (- 1 (/ (+ a b) modulo))))
    (implies
     (<= nu s)
     (frac-alpha-d-in alpha s (/ (+ a b) modulo) (- 1 (/ b modulo)))))))

(defrule aaa-invariant0-fwd
  (implies (aaa-invariant0 multiplier modulo maximum a b s nu)
           (and (natp multiplier)
                (posp modulo)
                (natp maximum)
                (integerp a)))
  :rule-classes :forward-chaining
  :enable aaa-invariant0)

(acl2::with-arith5-nonlinear-help
 (defruled aaa-invariant0-0-fwd
   (implies
    (aaa-invariant0 multiplier modulo maximum a b s 0)
    (and
     (= b modulo)
     (= (mod a b) (mod multiplier b))
     (= s 1)))
   :rule-classes :forward-chaining
   :enable (aaa-invariant0
            frac-alpha-d frac pos-rational-fix pos-rationalp fl)))

(acl2::with-arith5-help
 (defrule aaa-invariant0-suff-0
   (implies
    (and
     (natp multiplier)
     (posp modulo)
     (natp maximum)
     (posp a)
     (= (mod a modulo) (mod multiplier modulo))
     (= b modulo)
     (= s 1))
    (aaa-invariant0 multiplier modulo maximum a b s 0))
   :enable (aaa-invariant0 frac-alpha-d pos-rational-fix pos-rationalp
                           frac-alpha-d-in frac fl)))

(acl2::with-arith5-help
 (defrule aaa-invariant0-suff-1-1
   (implies
    (and
     (natp multiplier)
     (posp modulo)
     (natp maximum)
     (not (= a 0))
     (= (+ a b) modulo)
     (= a (mod multiplier modulo)))
    (aaa-invariant0 multiplier modulo maximum a b 1 1))
   :enable (aaa-invariant0 frac-alpha-d
                           frac-alpha-d-in
                           pos-rational-fix pos-rationalp frac)))

(acl2::with-arith5-help
 (rule
  (acl2::b*
   ((new-a (- a b))
    (new-s (+ s nu)))
   (implies
    (and
     (aaa-invariant0 multiplier modulo maximum a b s nu)
     (= nu 0)
     (> a b))
    (aaa-invariant0 multiplier modulo maximum new-a b new-s nu)))
  :enable aaa-invariant0-0-fwd))

(rule
 (acl2::b*
  ((new-b (- b a))
   (new-nu (+ s nu)))
  (implies
   (and
    (aaa-invariant0 multiplier modulo maximum a b s nu)
    (= nu 0)
    (< 0 a)
    (< a b))
   (aaa-invariant0 multiplier modulo maximum a new-b s new-nu)))
 :use (aaa-invariant0-0-fwd
       (:instance aaa-invariant0-suff-1-1
                  (b (- b a)))))

(defund aaa-invariant (multiplier modulo maximum a b s nu)
  (acl2::b*
   ((alpha (/ multiplier modulo)))
   (and
    (natp multiplier)
    (posp modulo)
    (natp maximum)
    (posp a)
    (posp b)
    (posp s)
    (posp nu)
    (<= (+ a b) modulo)
    (= (frac-alpha-d alpha s) (/ a modulo))
    (= (frac-alpha-d alpha nu) (- 1 (/ b modulo)))
    (implies
     (<= s nu)
     (frac-alpha-d-in alpha nu (/ a modulo) (- 1 (/ (+ a b) modulo))))
    (implies
     (<= nu s)
     (frac-alpha-d-in alpha s (/ (+ a b) modulo) (- 1 (/ b modulo)))))))

(acl2::with-arith5-help
 (rule
  (implies
   (and (aaa-invariant0 multiplier modulo maximum a b s nu)
        (not (= nu 0))
        )
   (aaa-invariant multiplier modulo maximum a b s nu))
  :enable (aaa-invariant0
           aaa-invariant)))
#|
(acl2::with-arith5-help
 (rule
  (acl2::b*
   ((new-b (- b a))
    (new-nu (+ s nu)))
   (implies
    (and
     (aaa-invariant0 multiplier modulo maximum a b s nu)
     (< a b))
    (aaa-invariant multiplier modulo maximum a new-b s new-nu)))
  :enable (aaa-invariant0 aaa-invariant frac frac-alpha-d-in frac-alpha-d fl)))
|#
(acl2::with-arith5-nonlinear-help
 (rule
  (acl2::b*
   ((new-b (- b a))
    (new-nu (+ s nu))
    )
   (implies
    (and
     (aaa-invariant a0 b0 maximum a b s nu)
     (> b a))
    (aaa-invariant a0 b0 maximum a new-b s new-nu)))
  :enable (aaa-invariant
           frac-alpha-d-in-monotonic-by-n)
  :cases ((<= s nu))
 :hints
 (("subgoal 2"
   :use (:instance frac-alpha-d-in-lemma
                   (alpha (/ a0 b0))
                   (n1 nu)
                   (n2 s)
                   (n (+ nu s))
                   (lo1 (/ (+ a b) b0))
                   (lo2 (/ (+ a b) b0))
                   (hi1 (- 1 (/ b b0)))
                   (hi2 (- 1 (/ b b0)))
                   (lo (/ a b0))
                   (hi (- 1 (/ b b0)))))
  ("subgoal 1"
   :use (:instance frac-alpha-d-in-lemma
                   (alpha (/ a0 b0))
                   (n1 s)
                   (n2 nu)
                   (n (+ nu s))
                   (lo1 (/ a b0))
                   (lo2 (/ a b0))
                   (hi1 (- 1 (/ (+ a b) b0)))
                   (hi2 (- 1 (/ (+ a b) b0)))
                   (lo (/ a b0))
                   (hi (- 1 (/ b b0))))))))

(acl2::with-arith5-nonlinear-help
 (rule
  (acl2::b*
   ((new-a (- a b))
    (new-s (+ s nu)))
   (implies
    (and
     (aaa-invariant a0 b0 maximum a b s nu)
     (< b a))
    (aaa-invariant a0 b0 maximum new-a b new-s nu)))
  :enable (aaa-invariant frac-alpha-d-in-monotonic-by-n)
  :cases ((<= s nu))
 :hints
 (("subgoal 2"
   :use (:instance frac-alpha-d-in-lemma
                   (alpha (/ a0 b0))
                   (n1 nu)
                   (n2 s)
                   (n (+ nu s))
                   (lo1 (/ (+ a b) b0))
                   (lo2 (/ (+ a b) b0))
                   (hi1 (- 1 (/ b b0)))
                   (hi2 (- 1 (/ b b0)))
                   (lo (/ a b0))
                   (hi (- 1 (/ b b0)))))
  ("subgoal 1"
   :use (:instance frac-alpha-d-in-lemma
                   (alpha (/ a0 b0))
                   (n1 s)
                   (n2 nu)
                   (n (+ nu s))
                   (lo1 (/ a b0))
                   (lo2 (/ a b0))
                   (hi1 (- 1 (/ (+ a b) b0)))
                   (hi2 (- 1 (/ (+ a b) b0)))
                   (lo (/ a b0))
                   (hi (- 1 (/ b b0))))))))

(define aaa
  ((maximum natp)
   (a posp)
   (b posp))
  :returns (mv i
               (a posp :rule-classes :type-prescription :hyp (posp a))
               (b posp :rule-classes :type-prescription :hyp (posp b))
               s
               nu)
  (aaa-aux maximum 0 a b 1 0))
#|
(acl2::b*
 ((a0 43)
  (b0 33)
  (maximum 100)
  (alpha (/ a0 b0))
  ((mv ?i a b ?s ?nu) (aaa maximum a0 b0))
  ((mv lo hi) (frac-alpha-d-nonzero-bound alpha (1+ maximum))))
 (list
  :a0 a0
  :b0 b0
  :maximum maximum
  :a a
  :b b
  :lo lo
  :lo0 (/ a b0)
  :hi0 (- 1 (/ b b0))
  :hi hi
  ))

(acl2::b*
 ((f (dp))
  (q -1000)
  (ulp2 (expt 2 q))
  (k (1- (ordD ulp2)))
  (ulpD (expt (D) k))
  (alpha (/ ulp2 ulpD))
  (a0 (if (<= 0 q) (expt 2 (- q k)) (expt 5 (- k))))
  (b0 (if (<= 0 q) (expt 5 k) (expt 2 (- k q))))
  (CbMax (+ (expt 2 (1+ (P f))) 2))
  (maximum (1- CbMax))
  ((mv i a b s nu) (aaa maximum a0 b0))
  ((mv lo hi) (frac-alpha-d-nonzero-bound alpha (1+ maximum))))
 (list
  :q q
  :k k
  :ulp2 ulp2
  :ulpD ulpD
  :alpha alpha
  :a0 a0
  :b0 b0
  :maximum maximum
  :i i
  :a a
  :b b
  :s s
  :nu nu
  :lo lo
  :lo0 (/ a b0)
  :hi0 (- 1 (/ b b0))
  :hi hi
  :dlo (- (/ a b0) lo)
  :dhi (- hi (- 1 (/ b b0)))
  ))

  (b0 33)
  (maximum 100)
  (alpha (/ a0 b0))
  ((mv ?i a b ?s ?nu) (aaa maximum a0 b0))
  ((mv lo hi) (frac-alpha-d-nonzero-bound alpha (1+ maximum))))
 (list
  :a0 a0
  :b0 b0
  :maximum maximum
  :a a
  :b b
  :lo lo
  :lo0 (/ a b0)
  :hi0 (- 1 (/ b b0))
  :hi hi
  ))
|#
(acl2::with-arith5-help
 (define frac-alpha-d-nonzero-bound-f-aaa-aux
   ((f formatp)
    (q integerp))
   :returns (mv (lo rationalp :rule-classes :type-prescription)
                (hi rationalp :rule-classes :type-prescription))
   :measure (nfix (- (1+ (ifix q)) (Qmin f)))
   :verify-guards nil
   (acl2::b*
    ((q (ifix q))
     ((unless (<= (Qmin f) q)) (mv 1 0))
     (ulp2 (expt 2 q))
     (k (1- (ordD ulp2)))
     (ulpD (expt (D) k))
     (alpha (/ ulp2 ulpD))
     (a0 (numerator alpha))
     (b0 (denominator alpha))
     (CbMax (+ (expt 2 (1+ (P f))) 2))
     (maximum (1- CBMax))
     ((mv ?i a b ?s ?nu) (aaa maximum a0 b0))
     (lo1 (/ a b0))
     (hi1 (- 1 (/ b b0)))
;     ((mv lo1 hi1) (frac-alpha-d-nonzero-bound alpha CbMax))
     ((mv lo2 hi2) (frac-alpha-d-nonzero-bound-f-aaa-aux f (1- q))))
    (mv (min lo1 lo2) (max hi1 hi2)))
   ///
   (fty::deffixequiv frac-alpha-d-nonzero-bound-f-aaa-aux)
   (verify-guards frac-alpha-d-nonzero-bound-f-aaa-aux)))

(define frac-alpha-d-nonzero-bound-f-aaa
  ((f formatp))
  :returns (mv (lo rationalp :rule-classes :type-prescription)
               (hi rationalp :rule-classes :type-prescription))
  (frac-alpha-d-nonzero-bound-f-aaa-aux f (Qmax f))
  ///
  (fty::deffixequiv frac-alpha-d-nonzero-bound-f))
#|
(acl2::b*
 ((f (dp))
  ((mv lo hi) (frac-alpha-d-nonzero-bound-f f))
  ((mv lo-aaa hi-aaa) (frac-alpha-d-nonzero-bound-f-aaa f)))
 (list
  :lo lo
  :lo-aaa lo-aaa
  :lo-cmp (signum (- lo-aaa lo))
  :hi1-aaa (- 1 hi-aaa)
  :hi1 (- 1 hi)
  :hi-cmp (signum (- hi-aaa hi))))

(frac-alpha-d-nonzero-bound-f (hp)) ; (1/65536 65535/65536)
(frac-alpha-d-nonzero-bound-f-aaa (hp)) ; (1/65536 4095/4096)

(frac-alpha-d-nonzero-bound-f (sp)) ; (43/152587890625 152587890578/152587890625)
(frac-alpha-d-nonzero-bound-f-aaa (sp)) ; (43/152587890625 1267650598488699631332441852745/1267650600228229401496703205376)

(time$ (frac-alpha-d-nonzero-bound-f (dp)))
; (ACL2::EV-REC ACL2::*RETURN-LAST-ARG3* ...) took
; 17.16 seconds realtime, 17.17 seconds runtime
; (357,099,520 bytes allocated).
; (1323359619378521/17763568394002504646778106689453125
;      17763568394002504644920130948187916/17763568394002504646778106689453125)
(time$ (frac-alpha-d-nonzero-bound-f-aaa (dp)))
; (ACL2::EV-REC ACL2::*RETURN-LAST-ARG3* ...) took
; 3.79 seconds realtime, 3.80 seconds runtime
; (306,681,952 bytes allocated).
; (1323359619378521/17763568394002504646778106689453125
;  44841550858394146256063851563197921964943774073523648718669290382652292491349440039780432629183833552/44841550858394146269559346665277316200968382140048504696226185084473314645947539247572422027587890625)

(time$ (frac-alpha-d-nonzero-bound-f (dp)))
(time$ (frac-alpha-d-nonzero-bound-f-aaa (dp)))
|#


#|
(aaa 0 43 33) ; (0 43 33 1 0)
(aaa 1 43 33) ; (2 10 23 1 1)
(aaa 2 43 33) ; (3 10 13 1 2)
(frac-alpha-d-nonzero-bound 43/33 1) ; (10/33 20/33)
(frac-alpha-d-nonzero-bound 43/33 2) ; (10/33 20/33)
(frac-alpha-d-nonzero-bound 43/33 3) ; (4/33 30/33)
(frac-alpha-d-nonzero-bound 43/33 4) ; (4/33 30/33)
(frac-alpha-d-nonzero-bound 43/33 5) ; (4/33 30/33)
(frac-alpha-d-nonzero-bound 43/33 6) ; (4/33 30/33)
(frac-alpha-d-nonzero-bound 43/33 7) ; (4/33 30/33)
(frac-alpha-d-nonzero-bound 43/33 8) ; (4/33 30/33)
(frac-alpha-d-nonzero-bound 43/33 9) ; (4/33 30/33)
(frac-alpha-d-nonzero-bound 43/33 10) ; (1/33 32/33)

(aaa 0 10 33) ; (0 10 33 1 0)
(aaa 1 10 33) ; (1 10 33 1 1)
(aaa 2 10 33) ; (2 10 13 1 2)
(aaa 3 10 33) ; (3 10 3 1 3)
(aaa 4 10 33) ; (4 7 3 4 3)
(aaa 5 10 33) ; (4 7 3 4 3)
(aaa 6 10 33) ; (4 7 3 4 3)
(aaa 7 10 33) ; (5 4 3 7 3)
(aaa 8 10 33) ; (5 4 3 7 3)
(aaa 9 10 33) ; (5 4 3 7 3)
(aaa 10 10 33) ; (6 1 3 10 3)
(aaa 11 10 33) ; (6 1 3 10 3)
(aaa 12 10 33) ; (6 1 3 10 3)
(aaa 13 10 33) ; (7 1 2 10 13)
(aaa 14 10 33) ; (7 1 2 10 13)
(aaa 15 10 33) ; (7 1 2 10 13)
(aaa 16 10 33) ; (7 1 2 10 13)
(aaa 17 10 33) ; (7 1 2 10 13)
(aaa 18 10 33) ; (7 1 2 10 13)
(aaa 19 10 33) ; (7 1 2 10 13)
(aaa 20 10 33) ; (7 1 2 10 13)
(aaa 21 10 33) ; (7 1 2 10 13)
(aaa 22 10 33) ; (7 1 2 10 13)
(aaa 23 10 33) ; (8 1 1 10 23)
(aaa 24 10 33) ; (8 1 1 10 23)
(aaa 25 10 33) ; (8 1 1 10 23)
(aaa 26 10 33) ; (8 1 1 10 23)
(aaa 27 10 33) ; (8 1 1 10 23)
(aaa 28 10 33) ; (8 1 1 10 23)
(aaa 29 10 33) ; (8 1 1 10 23)
(aaa 30 10 33) ; (8 1 1 10 23)
(aaa 31 10 33) ; (8 1 1 10 23)
(aaa 32 10 33) ; (8 1 1 10 23)
(aaa 33 10 33) ; (8 1 1 10 23)
(aaa 34 10 33) ; (8 1 1 10 23)

(aaa 0 4 10) ; (0 4 10 1 0)
(aaa 1 4 10) ; (1 4 6 1 1)
(aaa 2 4 10) ; (2 4 2 1 2)
(aaa 3 4 10) ; (3 2 2 3 2)
(aaa 4 4 10) ; (3 2 2 3 2)
(aaa 5 4 10) ; (3 2 2 3 2)
(aaa 6 4 10) ; (3 2 2 3 2)
(aaa 7 4 10) ; (3 2 2 3 2)
(aaa 8 4 10) ; (3 2 2 3 2)
(aaa 9 4 10) ; (3 2 2 3 2)
(aaa 10 4 10) ; (3 2 2 3 2)
(aaa 11 4 10) ; (3 2 2 3 2)
|#
(define bbb-aux
  ((maximum posp)
   (i natp)
   (a pos-rationalp)
   (b pos-rationalp)
   (s posp)
   (nu posp))
  :measure (nfix (- (acl2::pos-fix maximum)
                    (max (acl2::pos-fix s) (acl2::pos-fix nu))))
  :returns (mv (i natp :rule-classes :type-prescription)
               (a pos-rationalp :rule-classes :type-prescription)
               (b pos-rationalp :rule-classes :type-prescription)
               (s posp :rule-classes :type-prescription)
               (nu posp :rule-classes :type-prescription))
  (acl2::b*
   ((maximum (acl2::pos-fix maximum))
    (i (nfix i))
    (a (pos-rational-fix a))
    (b (pos-rational-fix b))
    (s (acl2::pos-fix s))
    (nu (acl2::pos-fix nu))
    (s+nu (+ s nu))
    (s+nu<=maximum (<= s+nu maximum))
    (a-b (- a b)))
   (cond ((and s+nu<=maximum (< a-b 0))
          (bbb-aux maximum (1+ i) a (- a-b) s s+nu))
         ((and s+nu<=maximum (< 0 a-b))
          (bbb-aux maximum (1+ i) a-b b s+nu nu))
         (t (mv i a b s nu))))
  ///
  (fty::deffixequiv bbb-aux))

(acl2::with-arith5-nonlinear-help
 (define bbb
  ((maximum natp)
   (alpha pos-rationalp))
  :returns (mv (a pos-rationalp :rule-classes :type-prescription)
               (b pos-rationalp :rule-classes :type-prescription))
  (acl2::b*
   ((a (frac-alpha-d alpha 1))
    ((when (or (zp maximum) (= a 0))) (mv 1 1))
    (b (- 1 a))
    ((mv ?i a b ?s ?nu) (bbb-aux maximum 0 a b 1 1)))
   (mv a b))
  :guard-hints (("goal" :in-theory (enable pos-rationalp)))
  ///
  (fty::deffixequiv bbb)))
#|
(bbb-aux 1 0 10/33 23/33 1 1) ; (0 10/33 23/33 1 1)
(bbb-aux 1 0 10/33 23/33 1 1) ; (0 10/33 23/33 1 1)
(bbb-aux 2 0 10/33 23/33 1 1) ; (0 10/33 13/33 1 2)
(bbb-aux 3 0 10/33 23/33 1 1) ; (0 10/33 1/11 1 3)
(bbb-aux 4 0 10/33 23/33 1 1) ; (0 7/33 1/11 4 3)
(bbb-aux 5 0 10/33 23/33 1 1) ; (0 7/33 1/11 4 3)
(bbb-aux 6 0 10/33 23/33 1 1) ; (0 7/33 1/11 4 3)
(bbb-aux 7 0 10/33 23/33 1 1) ; (0 4/33 1/11 7 3)
(bbb-aux 8 0 10/33 23/33 1 1) ; (0 4/33 1/11 7 3)
(bbb-aux 9 0 10/33 23/33 1 1) ; (0 4/33 1/11 7 3)
(bbb-aux 10 0 10/33 23/33 1 1) ; (0 1/33 1/11 10 3)
(bbb-aux 11 0 10/33 23/33 1 1) ; (0 1/33 1/11 10 3)
(bbb-aux 12 0 10/33 23/33 1 1) ; (0 1/33 1/11 10 3)
(bbb-aux 13 0 10/33 23/33 1 1) ; (0 1/33 2/33 10 13)
(bbb-aux 14 0 10/33 23/33 1 1) ; (0 1/33 2/33 10 13)
(bbb-aux 15 0 10/33 23/33 1 1) ; (0 1/33 2/33 10 13)
(bbb-aux 16 0 10/33 23/33 1 1) ; (0 1/33 2/33 10 13)
(bbb-aux 17 0 10/33 23/33 1 1) ; (0 1/33 2/33 10 13)
(bbb-aux 18 0 10/33 23/33 1 1) ; (0 1/33 2/33 10 13)
(bbb-aux 19 0 10/33 23/33 1 1) ; (0 1/33 2/33 10 13)
(bbb-aux 20 0 10/33 23/33 1 1) ; (0 1/33 2/33 10 13)
(bbb-aux 21 0 10/33 23/33 1 1) ; (0 1/33 2/33 10 13)
(bbb-aux 22 0 10/33 23/33 1 1) ; (0 1/33 2/33 10 13)
(bbb-aux 23 0 10/33 23/33 1 1) ; (0 1/33 1/33 10 23)

(bbb 20 43/33)
|#
(defun-sk grid-distance-ok (maximum alpha a b)
  (forall (x y)
          (implies
           (and (natp x)
                (<= x maximum)
                (integerp y))
           (acl2::b*
            ((alpha*x (* alpha x)))
            (or (<= y (- alpha*x a))
                (= y alpha*x)
                (>= y (+ alpha*x b)))))))
#|
Rune:         (:REWRITE GRID-DISTANCE-OK-NECC)
Enabled:      T
Hyps:         (NOT (IMPLIES (AND (NATP X)
                                 (<= X MAXIMUM)
                                 (INTEGERP Y))
                            (LET ((ALPHA*X (* ALPHA X)))
                                 (OR (<= Y (+ ALPHA*X (- A)))
                                     (= Y ALPHA*X)
                                     (<= (+ ALPHA*X B) Y)))))
Equiv:        EQUAL
Lhs:          (GRID-DISTANCE-OK MAXIMUM ALPHA A B)
Rhs:          NIL
Backchain-limit-lst: NIL
Subclass:     ACL2::BACKCHAIN
Loop-stopper: NIL

Rune:         (:DEFINITION GRID-DISTANCE-OK)
Enabled:      T
Hyps:         T
Equiv:        EQUAL
Lhs:          (GRID-DISTANCE-OK MAXIMUM ALPHA A B)
Rhs:          (MV-LET (X Y)
                      (GRID-DISTANCE-OK-WITNESS MAXIMUM ALPHA A B)
                      (OR (NOT (NATP X))
                          (COND ((< MAXIMUM X) T)
                                ((INTEGERP Y)
                                 (LET ((ALPHA*X (* ALPHA X)))
                                      (OR (NOT (< (+ ALPHA*X (- A)) Y))
                                          (EQUAL Y ALPHA*X)
                                          (NOT (< Y (+ ALPHA*X B))))))
                                (T T))))
Backchain-limit-lst: NIL
Subclass:     ACL2::DEFINITION
Clique:       NIL
Controller-alist: NIL

(DEFTHM GRID-DISTANCE-OK-NECC
  (IMPLIES (NOT (IMPLIES (AND (NATP X)
                              (<= X MAXIMUM)
                              (INTEGERP Y))
                         (ACL2::B* ((ALPHA*X (* ALPHA X)))
                                   (OR (<= Y (- ALPHA*X A))
                                       (= Y ALPHA*X)
                                       (>= Y (+ ALPHA*X B))))))
           (NOT (GRID-DISTANCE-OK MAXIMUM ALPHA A B))))
(DEFTHM  GRID-DISTANCE-OK-NECC
  (IMPLIES (GRID-DISTANCE-OK MAXIMUM ALPHA A B)
           (IMPLIES (AND (NATP X)
                         (<= X MAXIMUM)
                         (INTEGERP Y))
                    (ACL2::B* ((ALPHA*X (* ALPHA X)))
                              (OR (<= Y (- ALPHA*X A))
                                  (= Y ALPHA*X)
                                  (>= Y (+ ALPHA*X B))))))

|#
(defund bbb-aux-invariant (alpha maximum a b s nu)
  (and
   (pos-rationalp alpha)
   (posp maximum)
   (pos-rationalp a)
   (pos-rationalp b)
   (posp s)
   (posp nu)
   (<= (max s nu) maximum)
   (integerp (- (* alpha s) a))
   (integerp (+ (* alpha nu) b))
   (implies (<= s nu) (grid-distance-ok (1- nu) alpha a (+ a b)))
   (implies (<= nu s) (grid-distance-ok (1- s)  alpha (+ a b) b))))

(acl2::with-arith5-help
 (defrule  LEMMA-2-4-1
   (IMPLIES (AND (<= nu s)
                 (pos-rationalp b)
                 (integerp nu)
                 (integerp (+ (* alpha nu) b))
                 (GRID-DISTANCE-OK (+ -1 S) ALPHA (+ a b) b))
            (GRID-DISTANCE-OK (+ -1 NU S) ALPHA a b))
   :disable grid-distance-ok
   :cases ((> (mv-nth 0 (grid-distance-ok-witness (+ -1 nu s) alpha a b)) (1- s)))
   :use (:instance grid-distance-ok
                   (maximum (+ -1 nu s)))
   :hints
   (("subgoal 2" :use
     (:instance grid-distance-ok-necc
                (a (+ a b))
                (maximum (+ -1 s))
                (x (mv-nth 0 (grid-distance-ok-witness (+ -1 nu s) alpha a b)))
                (y (mv-nth 1 (grid-distance-ok-witness (+ -1 nu s) alpha a b)))))
    ("subgoal 1" :use
     (:instance grid-distance-ok-necc
                (a (+ a b))
                (maximum (+ -1 s))
                (x (- (mv-nth 0 (grid-distance-ok-witness (+ -1 nu s) alpha a b))
                      nu))
                (y (- (mv-nth 1 (grid-distance-ok-witness (+ -1 nu s) alpha a b))
                      (+ (* alpha nu) b))))))))

(acl2::with-arith5-help
 (defrule LEMMA-1-8-2
   (IMPLIES (AND (<= S NU)
                 (real/rationalp alpha)
                 (pos-rationalp a)
                 (integerp s)
                 (integerp (- (* alpha s) a))
                 (GRID-DISTANCE-OK (+ -1 NU) ALPHA a (+ a b)))
            (GRID-DISTANCE-OK (+ -1 NU S) ALPHA a B))
   :disable grid-distance-ok
   :cases ((> (mv-nth 0 (grid-distance-ok-witness (+ -1 s nu) alpha a b)) (1- nu)))
   :use (:instance grid-distance-ok
                   (maximum (+ -1 s nu)))
   :hints
   (("subgoal 2" :use
     (:instance grid-distance-ok-necc
                (b (+ a b))
                (maximum (+ -1 nu))
                (x (mv-nth 0 (grid-distance-ok-witness (+ -1 nu s) alpha a b)))
                (y (mv-nth 1 (grid-distance-ok-witness (+ -1 nu s) alpha a b)))))
    ("subgoal 1" :use
     (:instance grid-distance-ok-necc
                (b (+ a b))
                (maximum (+ -1 nu))
                (x (- (mv-nth 0 (grid-distance-ok-witness (+ -1 nu s) alpha a b))
                      s))
                (y (- (mv-nth 1 (grid-distance-ok-witness (+ -1 nu s) alpha a b))
                      (- (* alpha s) a))))))))

(acl2::with-arith5-help
 (rule
  (acl2::b*
   ((new-b (- b a))
    (new-nu (+ s nu)))
   (implies
    (and
     (bbb-aux-invariant alpha maximum a b s nu)
     (> b a)
     (<= (+ s nu) maximum))
    (bbb-aux-invariant alpha maximum a new-b s new-nu)))
  :enable (bbb-aux-invariant
           pos-rationalp)
  :disable (grid-distance-ok)
  :cases ((<= s nu))))

(acl2::with-arith5-help
 (rule
  (acl2::b*
   ((new-a (- a b))
    (new-s (+ s nu)))
   (implies
    (and
     (bbb-aux-invariant alpha maximum a b s nu)
     (> a b)
     (<= (+ s nu) maximum))
    (bbb-aux-invariant alpha maximum new-a b new-s nu)))
  :enable (bbb-aux-invariant
           pos-rationalp)
  :disable (grid-distance-ok)
  :cases ((<= s nu))))
