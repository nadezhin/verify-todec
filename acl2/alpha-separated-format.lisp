(in-package "RTL")
(include-book "section4")
(include-book "alpha-separated")

(local (include-book "rtl/rel11/support/basic" :dir :system))
(local (acl2::allow-arith5-help))

(acl2::with-arith5-help
 (define alpha-separated-format-aux
   ((f formatp)
    (q integerp))
   :returns (mv (a pos-rationalp :rule-classes :type-prescription)
                (b pos-rationalp :rule-classes :type-prescription))
   :measure (nfix (- (1+ (ifix q)) (Qmin f)))
   :verify-guards nil
   (acl2::b*
    ((q (ifix q))
     ((unless (<= (Qmin f) q)) (mv 1 1))
     (ulp2 (expt 2 q))
     (k (1- (ordD ulp2)))
     (ulpD (expt (D) k))
     (alpha (/ ulp2 ulpD))
     (CbMax (+ 2 (expt 2 (1+ (P f)))))
     ((mv a1 b1) (alpha-separated-rat-search CbMax alpha))
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
       (CbMax (+ 2 (expt 2 (1+ (P f)))))
       ((mv a b) (alpha-separated-format-aux f qmax)))
      (implies (and (integerp qmax)
                    (integerp q)
                    (<= (Qmin f) q)
                    (<= q qmax))
               (alpha-separated alpha Cbmax a b)))
     :rule-classes ()
     :induct (alpha-separated-format-aux f qmax)
     :enable alpha-separated-format-aux
     :hints
     (("subgoal *1/1" :cases ((< qmax q) (= qmax q) (> qmax q)))
      ("subgoal *1/1.2" :in-theory (disable alpha-separated-rat-search-correct)
       :use
       (:instance alpha-separated-rat-search-correct
                   (alpha (/ (expt 2 q) (expt (D) (1- (ordD (expt 2 q))))))
                   (maximum (+ (expt 2 (1+ (P f))) 2)))
       :expand (alpha-separated-format-aux f q))))))

(define alpha-separated-format
  ((f formatp))
  :returns (mv (a pos-rationalp :rule-classes :type-prescription)
               (b pos-rationalp :rule-classes :type-prescription))
  (alpha-separated-format-aux f (Qmax f))
  ///
  (fty::deffixequiv alpha-separated-format)
  (defrule alpha-separated-format-correct
    (acl2::b*
     ((ulp2 (expt 2 q))
      (k (1- (ordD ulp2)))
      (ulpD (expt (D) k))
      (alpha (/ ulp2 ulpD))
      (CbMax (+ 2 (expt 2 (1+ (P f)))))
      ((mv a b) (alpha-separated-format f)))
     (implies (and (integerp q)
                   (<= (Qmin f) q)
                   (<= q (Qmax f)))
              (alpha-separated alpha Cbmax a b)))
    :rule-classes ()
    :use (:instance alpha-separated-format-aux-correct
                    (qmax (Qmax f)))))
#|
(acl2::with-arith5-help
 (defrule frac-alpha-d-nonzero-bound-f-correct
   (acl2::b*
    ((ulp2 (expt 2 q))
     (k (1- (ordD ulp2)))
     (ulpD (expt (D) k))
     (alpha (/ ulp2 ulpD))
     (cbMax (+ (expt 2 (1+ (P f))) 2))
     ((mv a b) (alpha-separated-format f)))
    (implies (and (integerp q)
                  (<= (Qmin f) q)
                  (<= q (Qmax f))
                  (natp cb)
                  (<= cb cbMax)
                  (integerp m)
                  (< (- m b) (* alpha cb))
                  (< (* alpha cb) (+ m a)))
             (equal (* alpha cb) m)))
   :rule-classes ()
   :use
   (alpha-separated-format-correct
    (:instance alpha-separated-necc
               (alpha (/ (expt 2 q)
                         (expt (D) (1- (ordD (expt 2 q))))))
               (maximum (+ (expt 2 (1+ (P f))) 2))
               (x cb)
               (y m)
               (a (mv-nth 0 (alpha-separated-format f)))
               (b (mv-nth 1 (alpha-separated-format f)))))))
|#

;;; hp

(defconst *hp-a* 1/65536)
(defconst *hp-b* 1/4096)
(rule (and (= *hp-a* #fx1p-16)
           (= *hp-b* #fx1p-12)))

(defrule alpha-separated-hp-correct
 (acl2::b*
  ((f (hp))
   (ulp2 (expt 2 q))
   (k (1- (ordD ulp2)))
   (ulpD (expt (D) k))
   (alpha (/ ulp2 ulpD))
   (CbMax (+ 2 (expt 2 (1+ (P f))))))
  (implies (and (integerp q)
                (<= (Qmin f) q)
                (<= q (Qmax f)))
           (alpha-separated alpha Cbmax *hp-a* *hp-b*)))
 :rule-classes ()
 :enable hp
 :use (:instance alpha-separated-format-correct (f (hp))))

;;; sp

(defconst *sp-a* 43/152587890625)
(defconst *sp-b* 1739529770164261352631/1267650600228229401496703205376)
(rule (and (< #fx1.35D8FFE057C8Ap-32 *sp-a*)
           (< #fx1.79334CD629A6Cp-30 *sp-b*)))

(defrule alpha-separated-sp-correct
 (acl2::b*
  ((f (sp))
   (ulp2 (expt 2 q))
   (k (1- (ordD ulp2)))
   (ulpD (expt (D) k))
   (alpha (/ ulp2 ulpD))
   (CbMax (+ 2 (expt 2 (1+ (P f))))))
  (implies (and (integerp q)
                (<= (Qmin f) q)
                (<= q (Qmax f)))
           (alpha-separated alpha Cbmax *sp-a* *sp-b*)))
 :rule-classes ()
 :enable sp
 :use (:instance alpha-separated-format-correct (f (sp))))

(defconst *dp-a* 1323359619378521/17763568394002504646778106689453125)
(defconst *dp-b* 13495495102079394236024608066524855977556894701821022154598099207791989398404057073/44841550858394146269559346665277316200968382140048504696226185084473314645947539247572422027587890625)
(rule (and (< #fx1.5FCF304F8E95Cp-64 *dp-a*)
           (< #fx1.634F750135C33p-62 *dp-b*)))

;;; dp

(defrule alpha-separated-dp-correct
 (acl2::b*
  ((f (dp))
   (ulp2 (expt 2 q))
   (k (1- (ordD ulp2)))
   (ulpD (expt (D) k))
   (alpha (/ ulp2 ulpD))
   (CbMax (+ 2 (expt 2 (1+ (P f))))))
  (implies (and (integerp q)
                (<= (Qmin f) q)
                (<= q (Qmax f)))
           (alpha-separated alpha Cbmax *dp-a* *dp-b*)))
 :rule-classes ()
 :enable dp
 :use (:instance alpha-separated-format-correct (f (dp))))
