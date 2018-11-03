(in-package "RTL")
(include-book "section3")
(include-book "alpha-separated")

(local (include-book "rtl/rel11/support/basic" :dir :system))
(local (acl2::allow-arith5-help))

(acl2::with-arith5-help
 (define alpha-separated-format-aux
   ((f formatp)
    (q integerp))
   :returns (mv (a real/rationalp :rule-classes :type-prescription)
                (b real/rationalp :rule-classes :type-prescription))
   :measure (nfix (- (1+ (ifix q)) (Qmin f)))
   :verify-guards nil
   (acl2::b*
    ((q (ifix q))
     ((unless (<= (Qmin f) q)) (mv 1 1))
     (ulp2 (expt 2 q))
     (k (1- (ordD ulp2)))
     (ulpD (expt (D) k))
     (alpha (/ ulp2 ulpD))
     (CbMax (+ (expt 2 (1+ (P f))) 2))
     ((mv a1 b1) (alpha-separated-search CbMax alpha))
     ((mv a2 b2) (alpha-separated-format-aux f (1- q))))
    (mv (min a1 a2) (min b1 b2)))
   ///
   (fty::deffixequiv alpha-separated-format-aux)
   (verify-guards alpha-separated-format-aux)
   (defrule alpha-separated-format-aux-linear
     (and (<= (mv-nth 0 (alpha-separated-format-aux f q)) 1)
          (<= (mv-nth 1 (alpha-separated-format-aux f q)) 1))
     :rule-classes :linear)
   (defrule alpha-separated-format-aux-correct
     (acl2::b*
      ((ulp2 (expt 2 q))
       (k (1- (ordD ulp2)))
       (ulpD (expt (D) k))
       (alpha (/ ulp2 ulpD))
       (CbMax (+ (expt 2 (1+ (P f))) 2))
       ((mv a b) (alpha-separated-format-aux f qmax)))
      (implies (and (integerp qmax)
                    (integerp q)
                    (<= (Qmin f) q)
                    (<= q qmax))
               (alpha-separated alpha Cbmax a b)))
     :induct (alpha-separated-format-aux f qmax)
     :enable alpha-separated-format-aux
     :hints
     (("subgoal *1/1" :cases ((< qmax q) (= qmax q) (> qmax q)))
      ("subgoal *1/1.2" :in-theory (disable  alpha-separated-search-correct)
       :use
       (:instance alpha-separated-search-correct
                   (alpha (/ (expt 2 q) (expt (D) (1- (ordD (expt 2 q))))))
                   (maximum (+ (expt 2 (1+ (P f))) 2)))
       :expand (alpha-separated-format-aux f q))))))

(define alpha-separated-format
  ((f formatp))
  :returns (mv (a real/rationalp :rule-classes :type-prescription)
               (b real/rationalp :rule-classes :type-prescription))
  (alpha-separated-format-aux f (Qmax f))
  ///
  (fty::deffixequiv alpha-separated-format)
  (acl2::with-arith5-help
   (defrule frac-alpha-d-nonzero-bound-f-correct
     (acl2::b*
      ((ulp2 (expt 2 (+ qb 1)))
       (k (1- (ordD ulp2)))
       (ulpD (expt (D) k))
       (alpha (/ ulp2 ulpD))
       (cbMax (+ (expt 2 (1+ (P f))) 2))
       ((mv a b) (alpha-separated-format f)))
      (implies (and (integerp qb)
                   (<= (- (Qmin f) 1) qb)
                   (<= qb (- (Qmax f) 1))
                   (natp cb)
                   (<= cb cbMax)
                   (integerp m)
                   (< (- m b) (* alpha cb))
                   (< (* alpha cb) (+ m a)))
               (equal (* alpha cb) m)))
     :rule-classes ()
     :use
     ((:instance alpha-separated-necc
                 (alpha (/ (expt 2 (+ qb 1))
                           (expt (D) (1- (ordD (expt 2 (+ qb 1)))))))
                 (maximum (+ (expt 2 (1+ (P f))) 2))
                 (x cb)
                 (y m)
                 (a (mv-nth 0 (alpha-separated-format f)))
                 (b (mv-nth 1 (alpha-separated-format f))))
      (:instance alpha-separated-format-aux-correct
                 (q (+ qb 1))
                 (qmax (Qmax f)))))))

(defrule frac-alpha-d-nonzero-bound-hp-correct
  (acl2::b*
   ((f (hp))
    (a 1/65536)
    (b 1/4096)
    (ulp2 (expt 2 (+ qb 1)))
    (r (1- (ordD ulp2)))
    (ulpD (expt (D) r))
    (alpha (/ ulp2 ulpD))
    (cbMax (+ (expt 2 (1+ (P f))) 2)))
   (implies (and (integerp qb)
                 (<= (- (Qmin f) 1) qb)
                 (<= qb (- (Qmax f) 1))
                 (natp cb)
                 (<= cb cbMax)
                 (integerp m)
                 (< (- m b) (* alpha cb))
                 (< (* alpha cb) (+ m a)))
            (equal (* alpha cb) m)))
  :rule-classes ()
  :enable hp
  :use (:instance frac-alpha-d-nonzero-bound-f-correct (f (hp))))

(rule
 (and (= #fx1p-16
         1/65536)
      (= #fx1p-12
         1/4096)))

(defrule frac-alpha-d-nonzero-bound-sp-correct
  (acl2::b*
   ((f (sp))
    (a 43/152587890625)
    (b 1739529770164261352631/1267650600228229401496703205376)
    (ulp2 (expt 2 (+ qb 1)))
    (r (1- (ordD ulp2)))
    (ulpD (expt (D) r))
    (alpha (/ ulp2 ulpD))
    (cbMax (+ (expt 2 (1+ (P f))) 2)))
   (implies (and (integerp qb)
                 (<= (- (Qmin f) 1) qb)
                 (<= qb (- (Qmax f) 1))
                 (natp cb)
                 (<= cb cbMax)
                 (integerp m)
                 (< (- m b) (* alpha cb))
                 (< (* alpha cb) (+ m a)))
            (equal (* alpha cb) m)))
  :rule-classes ()
  :enable sp
  :use (:instance frac-alpha-d-nonzero-bound-f-correct (f (sp))))

(rule
 (and (< #fx1.35D8FFE057C8Ap-32
         43/152587890625)
      (< #fx1.79334CD629A6Cp-30
         1739529770164261352631/1267650600228229401496703205376)))

(defrule frac-alpha-d-nonzero-bound-dp-correct
  (acl2::b*
   ((f (dp))
    (a 1323359619378521/17763568394002504646778106689453125)
    (b 13495495102079394236024608066524855977556894701821022154598099207791989398404057073/44841550858394146269559346665277316200968382140048504696226185084473314645947539247572422027587890625)
    (ulp2 (expt 2 (+ qb 1)))
    (r (1- (ordD ulp2)))
    (ulpD (expt (D) r))
    (alpha (/ ulp2 ulpD))
    (cbMax (+ (expt 2 (1+ (P f))) 2)))
   (implies (and (integerp qb)
                 (<= (- (Qmin f) 1) qb)
                 (<= qb (- (Qmax f) 1))
                 (natp cb)
                 (<= cb cbMax)
                 (integerp m)
                 (< (- m b) (* alpha cb))
                 (< (* alpha cb) (+ m a)))
            (equal (* alpha cb) m)))
  :rule-classes ()
  :enable dp
  :use (:instance frac-alpha-d-nonzero-bound-f-correct (f (dp))))

(rule
 (and (< #fx1.5FCF304F8E95Cp-64
         1323359619378521/17763568394002504646778106689453125)
      (< #fx1.634F750135C33p-62
         13495495102079394236024608066524855977556894701821022154598099207791989398404057073/44841550858394146269559346665277316200968382140048504696226185084473314645947539247572422027587890625)))
