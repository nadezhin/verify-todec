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

(define regular
  ((v pos-rationalp)
   (f formatp))
  :returns (regular booleanp :rule-classes ())
  (or (not (= (c v f) (2^{P-1} f)))
      (= (q v f) (Qmin f)))
  ///
  (fty::deffixequiv regular))

(acl2::with-arith5-help
 (defruled k-as-regular
   (equal (k v f)
          (1- (ordD (* (if (regular v f) 1 3/4)
                       (expt 2 (q v f))))))
   :enable (k wid-Rv-as-c-q ordD regular)))

(acl2::with-arith5-help
 (defrule V_-fraction-gen
  (acl2::b*
   ((q (q v f))
    (c (c v f))
    (ulp2 (expt 2 q))
    (CbMax (+ 2 (expt 2 (1+ (P f)))))
    (k (k v f))
    (ulpD (expt (D) k))
    (alpha (/ (if (regular v f) ulp2 (* 1/2 ulp2))
              ulpD))
    (v_ (/ (* (+ c-incr c) ulp2) ulpD))
    (fraction (- (* 2 v_) (floor (* 2 v_) 1))))
   (implies (and (finite-positive-binary-p v f)
                 (alpha-separated alpha Cbmax a b)
                 (< eps a)
                 (< eps b)
                 (real/rationalp a)
                 (real/rationalp b)
                 (real/rationalp eps)
                 (if (regular v f)
                     (member c-incr '(-1/2 0 1/2))
                   (member c-incr '(-1/4 0 1/2))))
            (or (= fraction 0)
                (and (< eps fraction) (< fraction (- 1 eps))))))
  :rule-classes ()
  :enable k-as-regular
  :cases ((regular v f))
  :hints
  (("subgoal 2" :use
    (:instance alpha-separated-fraction
               (alpha (/ (* 1/2 (expt 2 (q v f)))
                         (expt (D) (k v f))))
               (x (* 4 (+ c-incr (c v f))))
               (maximum (+ 2 (expt 2 (1+ (P f)))))))
   ("subgoal 1" :use
    (:instance alpha-separated-fraction
               (alpha (/ (expt 2 (q v f))
                         (expt (D) (k v f))))
               (x (* 2 (+ c-incr (c v f))))
               (maximum (+ 2 (expt 2 (1+ (P f))))))))
  :prep-lemmas
  ((defrule lemma1
     (implies (not (regular v f))
              (equal (c v f) (expt 2 (1- (P f)))))
     :enable (regular 2^{P-1}))
  (defrule lemma2
    (implies (finite-positive-binary-p v f)
             (posp (c v f)))
    :rule-classes :type-prescription
    :use (:instance c-type-when-finite-positive-binary
                    (x v)))
  (defrule lemma3
    (implies (finite-positive-binary-p v f)
             (<= (c v f) (1- (expt 2 (P f)))))
    :rule-classes :linear
    :enable (CMax 2^{P-1}))
  (acl2::with-arith5-nonlinear-help
   (defrule lemma3a
     (implies (finite-positive-binary-p v f)
              (<= (* 2 (c v f)) (- (expt 2 (1+ (P f))) 2)))
     :rule-classes :linear)))))

(acl2::with-arith5-help
 (defrule V_-fraction
  (acl2::b*
   ((q (q v f))
    (ulp2 (expt 2 q))
    (CbMax (+ 2 (expt 2 (1+ (P f)))))
    (k (k v f))
    (ulpD (expt (D) k))
    (alpha (/ (if (regular v f) ulp2 (* 1/2 ulp2)) ulpD))
    (2*V_ (* 2 (V_ v f)))
    (fraction (- 2*V_ (floor 2*V_ 1))))
   (implies (and (finite-positive-binary-p v f)
                 (alpha-separated alpha Cbmax a b)
                 (< eps a)
                 (< eps b)
                 (real/rationalp a)
                 (real/rationalp b)
                 (real/rationalp eps))
            (or (= fraction 0)
                (and (< eps fraction) (< fraction (- 1 eps))))))
  :rule-classes ()
  :enable (2^{P-1} k-as-regular)
  :disable acl2::|(floor (* 2 x) 1)|
  :use (:instance V_-fraction-gen
                  (c-incr 0))
  :prep-lemmas
  ((defrule lemma
     (implies (finite-positive-binary-p v f)
              (equal (V_ v f)
                     (* (c v f)
                        (expt 2 (q v f))
                        (expt (D) (- (k v f))))))
    :enable (V_ 2^{P-1})
    :use (:instance finite-positive-binary-necc
                    (x v))))))

(defrule Vl_-fraction
  (acl2::b*
   ((q (q v f))
    (ulp2 (expt 2 q))
    (CbMax (+ 2 (expt 2 (1+ (P f)))))
    (k (k v f))
    (ulpD (expt (D) k))
    (alpha (/ (if (regular v f) ulp2 (* 1/2 ulp2)) ulpD))
    (2*Vl_ (* 2 (Vl_ v f)))
    (fraction (- 2*Vl_ (floor 2*Vl_ 1))))
   (implies (and (finite-positive-binary-p v f)
                 (alpha-separated alpha Cbmax a b)
                 (< eps a)
                 (< eps b)
                 (real/rationalp a)
                 (real/rationalp b)
                 (real/rationalp eps))
            (or (= fraction 0)
                (and (< eps fraction) (< fraction (- 1 eps))))))
  :rule-classes ()
  :enable (2^{P-1} k-as-regular)
  :use (:instance V_-fraction-gen
                  (c-incr (if (regular v f) -1/2 -1/4)))
  :prep-lemmas
  ((acl2::with-arith5-help
    (defrule lemma1
     (implies (finite-positive-binary-p v f)
              (equal (Vl_ v f)
                     (* (+ (if (regular v f) -1/2 -1/4) (c v f))
                        (expt 2 (q v f))
                        (expt (D) (- (k v f))))))
    :enable (Vl_ Vl-alt regular)))
   (acl2::with-arith5-help
    (defrule lemma2
      (equal (/ (expt (D) (1- (ordD ulp))))
             (* (expt (D) (- 1 (ordD ulp)))))))))

(defrule Vr_-fraction
  (acl2::b*
   ((q (q v f))
    (ulp2 (expt 2 q))
    (CbMax (+ 2 (expt 2 (1+ (P f)))))
    (k (k v f))
    (ulpD (expt (D) k))
    (alpha (/ (if (regular v f) ulp2 (* 1/2 ulp2)) ulpD))
    (2*Vr_ (* 2 (Vr_ v f)))
    (fraction (- 2*Vr_ (floor 2*Vr_ 1))))
   (implies (and (finite-positive-binary-p v f)
                 (alpha-separated alpha Cbmax a b)
                 (< eps a)
                 (< eps b)
                 (real/rationalp a)
                 (real/rationalp b)
                 (real/rationalp eps))
            (or (= fraction 0)
                (and (< eps fraction) (< fraction (- 1 eps))))))
  :rule-classes ()
  :enable (2^{P-1} k-as-regular)
  :disable (floor expt)
  :use (:instance V_-fraction-gen
                  (c-incr 1/2))
  :prep-lemmas
  ((acl2::with-arith5-help
    (defrule lemma1
     (implies (finite-positive-binary-p v f)
              (equal (Vr_ v f)
                     (* (+ 1/2 (c v f))
                        (expt 2 (q v f))
                        (expt (D) (- (k v f))))))
    :enable (Vr_ Vr)))
   (acl2::with-arith5-help
    (defrule lemma2
      (equal (/ (expt (D) (1- (ordD ulp))))
             (* (expt (D) (- 1 (ordD ulp)))))))))

; Result 17 for doubles

(defrule result17-V_-dp
  (acl2::b*
   ((f (dp))
    (eps #fx1p-64)
    (2*V_ (* 2 (V_ v f)))
    (fraction (- 2*V_ (floor 2*V_ 1))))
   (implies (finite-positive-binary-p v f)
            (or (= fraction 0)
                (and (< eps fraction) (< fraction (- 1 eps))))))
  :rule-classes ()
  :enable k-as-regular
  :use ((:instance alpha-separated-dp-correct
                   (q (q v (dp))))
        (:instance V_-fraction
                   (f (dp))
                   (eps #fx1p-64)
                   (a *dp-a*)
                   (b *dp-b*))))

(defrule result17-Vl_-dp
  (acl2::b*
   ((f (dp))
    (eps #fx1p-64)
    (2*Vl_ (* 2 (Vl_ v f)))
    (fraction (- 2*Vl_ (floor 2*Vl_ 1))))
   (implies (finite-positive-binary-p v f)
            (or (= fraction 0)
                (and (< eps fraction) (< fraction (- 1 eps))))))
  :rule-classes ()
  :enable k-as-regular
  :use ((:instance alpha-separated-dp-correct
                   (q (q v (dp))))
        (:instance Vl_-fraction
                   (f (dp))
                   (eps #fx1p-64)
                   (a *dp-a*)
                   (b *dp-b*))))

(defrule result17-Vr_-dp
  (acl2::b*
   ((f (dp))
    (eps #fx1p-64)
    (2*Vr_ (* 2 (Vr_ v f)))
    (fraction (- 2*Vr_ (floor 2*Vr_ 1))))
   (implies (finite-positive-binary-p v f)
            (or (= fraction 0)
                (and (< eps fraction) (< fraction (- 1 eps))))))
  :rule-classes ()
  :enable k-as-regular
  :use ((:instance alpha-separated-dp-correct
                   (q (q v (dp))))
        (:instance Vr_-fraction
                   (f (dp))
                   (eps #fx1p-64)
                   (a *dp-a*)
                   (b *dp-b*))))

; Result 17 for floats

(defrule result17-V_-sp
  (acl2::b*
   ((f (sp))
    (eps #fx1p-32)
    (2*V_ (* 2 (V_ v f)))
    (fraction (- 2*V_ (floor 2*V_ 1))))
   (implies (finite-positive-binary-p v f)
            (or (= fraction 0)
                (and (< eps fraction) (< fraction (- 1 eps))))))
  :rule-classes ()
  :enable k-as-regular
  :use ((:instance alpha-separated-sp-correct
                   (q (q v (sp))))
        (:instance V_-fraction
                   (f (sp))
                   (eps #fx1p-32)
                   (a *sp-a*)
                   (b *sp-b*))))

(defrule result17-Vl_-sp
  (acl2::b*
   ((f (sp))
    (eps #fx1p-32)
    (2*Vl_ (* 2 (Vl_ v f)))
    (fraction (- 2*Vl_ (floor 2*Vl_ 1))))
   (implies (finite-positive-binary-p v f)
            (or (= fraction 0)
                (and (< eps fraction) (< fraction (- 1 eps))))))
  :rule-classes ()
  :enable k-as-regular
  :use ((:instance alpha-separated-sp-correct
                   (q (q v (sp))))
        (:instance Vl_-fraction
                   (f (sp))
                   (eps #fx1p-32)
                   (a *sp-a*)
                   (b *sp-b*))))

(defrule result17-Vr_-sp
  (acl2::b*
   ((f (sp))
    (eps #fx1p-32)
    (2*Vr_ (* 2 (Vr_ v f)))
    (fraction (- 2*Vr_ (floor 2*Vr_ 1))))
   (implies (finite-positive-binary-p v f)
            (or (= fraction 0)
                (and (< eps fraction) (< fraction (- 1 eps))))))
  :rule-classes ()
  :enable k-as-regular
  :use ((:instance alpha-separated-sp-correct
                   (q (q v (sp))))
        (:instance Vr_-fraction
                   (f (sp))
                   (eps #fx1p-32)
                   (a *sp-a*)
                   (b *sp-b*))))
