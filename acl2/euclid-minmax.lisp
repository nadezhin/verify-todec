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

#|
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
|#
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
   (cond
    ((and s+nu<=maximum (< a-b 0)) (bbb-aux maximum (1+ i) a (- a-b) s s+nu))
    ((and s+nu<=maximum (< 0 a-b)) (bbb-aux maximum (1+ i) a-b b s+nu nu))
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

(acl2::with-arith5-nonlinear-help
 (defrule LEMMA-aaaa
   (implies (and (alpha-separated alpha maximum1 A a+b)
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

(acl2::with-arith5-help
; (rule
 (defrule LEMMA-bbb
   (IMPLIES (AND (ALPHA-SEPARATED ALPHA maximum1 a+b B)
                 (RATIONALP ALPHA)
               (RATIONALP A)
               (RATIONALP B)
               (integerp maximum)
               (integerp maximum1)
               (<= maximum1 maximum)
               (<= maximum (1+ (* 2 maximum1)))
               (<= 0 b)
               (= a+b (+ a b))
               (INTEGERP (+ (* ALPHA (- maximum maximum1)) b)))
          (ALPHA-SEPARATED ALPHA maximum a b))
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


(defund bbb-aux-invariant2 (alpha a b s nu)
;(defund bbb-aux-invariant2 (alpha maximum a b s nu)
  (and
   (real/rationalp alpha)
   (real/rationalp a)
   (real/rationalp b)
   (posp s)
   (posp nu)
   (< 0 a)
   (< 0 b)
;   (<= (max s nu) maximum)
   (integerp (- (* alpha s) a))
   (integerp (+ (* alpha nu) b))
   (alpha-separated alpha (+ -1 s nu) a b)))

(acl2::with-arith5-nonlinear-help
 (rule
  (acl2::b*
   ((new-b (- b a))
    (new-nu (+ s nu)))
   (implies
    (and
     (bbb-aux-invariant2 alpha a b s nu)
     (> b a))
    (bbb-aux-invariant2 alpha a new-b s new-nu)))
  :enable bbb-aux-invariant2))


(acl2::with-arith5-nonlinear-help
 (rule
  (acl2::b*
   ((new-a (- a b))
    (new-s (+ s nu)))
   (implies
    (and
     (bbb-aux-invariant2 alpha a b s nu)
     (> a b))
    (bbb-aux-invariant2 alpha new-a b new-s nu)))
  :enable bbb-aux-invariant2))

(acl2::with-arith5-help
 (defrule aaaaaa
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
    (implies (and (posp period)
                  )
             (equal (+ (* alpha (mod x period))
                       (* alpha period (floor x period)))
                    (* alpha x))))))))

(rule
 (implies (and (bbb-aux-invariant2 alpha a b s nu)
               (integerp maximum)
               (or (= a b)
                   (> (+ s nu) maximum)))
          (alpha-separated alpha maximum a b))
 :enable bbb-aux-invariant2
 :hints
 (("subgoal 2" :use (:instance aaaaaa
                              (period (+ nu s))))
  )
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
                (integerp (+ x y)))))
    )))
 )
