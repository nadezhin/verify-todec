(in-package "RTL")
(include-book "section8")
(include-book "alpha-separated-format")

;(local (include-book "rtl/rel11/support/basic" :dir :system))
(local (include-book "rtl/rel11/support/float" :dir :system))
(local (acl2::allow-arith5-help))

; Definition 7

(define V_
  ((v pos-rationalp)
   (f formatp))
  :returns (V_ pos-rationalp :rule-classes ())
  (* (pos-rational-fix v)
     (expt (D) (- (k v f))))
  ///
  (fty::deffixequiv V_))

(define Vl_
  ((v pos-rationalp)
   (f formatp))
  :returns (Vl_ rationalp :rule-classes ())
  (* (vl v f)
     (expt (D) (- (k v f))))
  ///
  (fty::deffixequiv Vl_))

(define Vr_
  ((v pos-rationalp)
   (f formatp))
  :returns (Vr_ pos-rationalp :rule-classes ())
  (* (vr v f)
     (expt (D) (- (k v f))))
  ///
  (fty::deffixequiv Vr_))

(local
 (acl2::with-arith5-help
  (defrule alpha-separated-fraction
    (implies (and (alpha-separated alpha maximum a b)
                  (natp x)
                  (<= x maximum)
                  (< eps a)
                  (< eps b)
                  (real/rationalp alpha)
                  (< 0 alpha)
                  (real/rationalp a)
                  (real/rationalp b)
                  (real/rationalp eps))
             (acl2::b*
              ((alpha*x (* alpha x))
               (fraction (- alpha*x (floor alpha*x 1))))
              (or (= fraction 0)
                  (and (< eps fraction) (< fraction (- 1 eps))))))
    :rule-classes ()
    :use ((:instance alpha-separated-necc
                     (y (floor (* alpha x) 1)))
          (:instance alpha-separated-necc
                     (y (1+ (floor (* alpha x) 1))))))))

#|
(acl2::with-arith5-help
 (defrule aaa
  (acl2::b*
   ((q (q v f))
    (ulp2 (expt 2 q))
    (CbMax (+ 2 (expt 2 (1+ (P f)))))
    (k-regular (1- (ordD ulp2)))
;    (k-regular (k v f))
    (ulpD-regular (expt (D) k-regular))
    (alpha-regular (/ ulp2 ulpD-regular))
    (2*V_ (* 2 (V_ v f)))
    (fraction (- 2*V_ (floor 2*V_ 1))))
   (implies (and (finite-positive-binary-p v f)
                 (alpha-separated alpha-regular Cbmax a b)
                 (< eps a)
                 (< eps b)
                 (real/rationalp a)
                 (real/rationalp b)
                 (real/rationalp eps))
            (or (= fraction 0)
                (and (< eps fraction) (< fraction (- 1 eps))))))
  :rule-classes ()
  :disable (acl2::|(floor (* 2 x) 1)|)
  :use (:instance alpha-separated-fraction
                  (alpha (/ (expt 2 (q v f)) (expt (D) (k v f))))
                  (x (* 2 (c v f)))
                  (maximum (+ 2 (expt 2 (1+ (P f))))))
 :prep-lemmas
 ((acl2::with-arith5-nonlinear-help
   (defrule lemma1
     (<= (* 2 (c v f)) (+ 2 (expt 2 (1+ (p f)))))
    :enable 2^{P-1}
    :use (:instance c-linear
                    (x v))))
  (defrule lemma2
    (implies (finite-positive-binary-p v f)
             (posp (c v f)))
    :use (:instance c-type-when-finite-positive-binary
                    (x v)))
  (defrule lemma3
    (implies (finite-positive-binary-p v f)
             (equal (V_ v f)
                    (* (c v f)
                       (expt 2 (q v f))
                       (expt (D) (- (k v f))))))
    :enable V_
    :use (:instance finite-positive-binary-necc
                    (x v)))
  (defrule lemma4
    (
  )))


(rule
 (acl2::b*
  ((f (dp))
   (eps #fx1p-64)
;     (q (q v f))
;    (ulp2 (expt 2 q))
;    (CbMax (+ 2 (expt 2 (1+ (P f)))))
;    (k-regular (k v f))
;    (ulpD-regular (expt (D) k-regular))
;    (alpha-regular (/ ulp2 ulpD-regular))
   (2*V_ (* 2 (V_ v f)))
   (fraction (- 2*V_ (floor 2*V_ 1))))
   (implies (finite-positive-binary-p v f)
;                 (alpha-separated alpha-regular Cbmax a b)
;                 (< eps a)
;                 (< eps b)
;                 (real/rationalp a)
;                 (real/rationalp b)
;                 (real/rationalp eps))
            (or (= fraction 0)
                (and (< eps fraction) (< fraction (- 1 eps))))))
 :use ((:instance alpha-separated-dp-correct
                  (q (q v (dp))))
       (:instance aaa
                  (f (dp))
                  (a *dp-a*)
                  (b *dp-b*)))
 :disable (floor expt)
 )
|#
