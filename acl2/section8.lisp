(in-package "RTL")
(include-book "section7")

(local (include-book "rtl/rel11/support/basic" :dir :system))
(local (include-book "rtl/rel11/support/bits" :dir :system))
(local (include-book "rtl/rel11/support/float" :dir :system))
(local (include-book "rtl/rel11/support/reps" :dir :system))
(local (acl2::allow-arith5-help))

(define H
  ((f formatp))
  :returns (H (and (integerp H) (< 1 H)) :rule-classes :type-prescription
              :hints (("goal" :use (:instance result-1-4
                                              (x 1)
                                              (y (* 2 (2^{P-1} f)))))))
  (+ (ordD (* 2 (2^{P-1} f))) 1)
  ///
  (fty::deffixequiv H)
  (acl2::with-arith5-nonlinear-help
   (defrule H-def
     (implies (integerp n)
              (equal (> (expt (D) (- n 1)) (* 2 (2^{P-1} f)))
                     (>= n (H f))))
     :rule-classes ()
     :cases ((>= n (H f))
             (<= n (1- (H f))))
     :use (:instance result-1-3
                     (x (* 2 (2^{P-1} f)))
                     (k (ordD (* 2 (2^{P-1} f))))))))

(rule
 (and (= (H (hp)) 5)
      (= (H (sp)) 9)
      (= (H (dp)) 17)
      (= (H (ep)) 21))
 :enable (hp sp dp ep))

; Matula proved result-3 for infinite exponent range.
; For finite exponent range the second part of result 3 is also true,
; but the first part may be false for some format.
; We give an example of such format.
(defconst *format-for-result-3* '(nil 4 2))

(rule
 (and (formatp *format-for-result-3*)
      (= (P *format-for-result-3*) 4)
      (= (W_ *format-for-result-3*) 2)
      (= (H *format-for-result-3*) 3)
      (= (Qmin *format-for-result-3*) -3)
      (= (Qmax *format-for-result-3*) -2)))

; For all finite-positive-binary v of format *format-for-result-3* algo1 returns
; decimal of length H-1 which is rounded back to v.
; It is proved by enumeration of all members of the format.

(defrule result-3-1-incorrect-for-artifical-format
 (let* ((f *format-for-result-3*)
        (i (- (H *format-for-result-3*) 1))
        (dv (algo1 i v f)))
   (implies (finite-positive-binary-p v f)
            (and (has-D-length i dv)
                 (in-tau-intervalp dv (Rv v f)))))
 :use (:instance finite-positive-binary-necc
                 (x v)
                 (f *format-for-result-3*))

 :cases ((= (q v *format-for-result-3*) (Qmin *format-for-result-3*))
         (= (q v *format-for-result-3*) (Qmax *format-for-result-3*)))
 :hints
 (("subgoal 2" :cases ; enumerate all c for Qmin
   ((= (c v *format-for-result-3*) 1)
    (= (c v *format-for-result-3*) 2)
    (= (c v *format-for-result-3*) 3)
    (= (c v *format-for-result-3*) 4)
    (= (c v *format-for-result-3*) 5)
    (= (c v *format-for-result-3*) 6)
    (= (c v *format-for-result-3*) 7)
    (= (c v *format-for-result-3*) 8)
    (= (c v *format-for-result-3*) 9)
    (= (c v *format-for-result-3*) 10)
    (= (c v *format-for-result-3*) 11)
    (= (c v *format-for-result-3*) 12)
    (= (c v *format-for-result-3*) 13)
    (= (c v *format-for-result-3*) 14)
    (= (c v *format-for-result-3*) 15)))
  ("subgoal 1" :cases ; enumerate all c for Qmax
   ((= (c v *format-for-result-3*) 8)
    (= (c v *format-for-result-3*) 9)
    (= (c v *format-for-result-3*) 10)
    (= (c v *format-for-result-3*) 11)
    (= (c v *format-for-result-3*) 12)
    (= (c v *format-for-result-3*) 13)
    (= (c v *format-for-result-3*) 14)
    (= (c v *format-for-result-3*) 15)))))

; We show that the the first part of result-3 is true
; for some partucular formats including double-precision format.
; For each format we give a some positive finite member v of a format,
; such that each decimal in Rv has length >= H.
; Below is a form we used to search for such v.
#|
(let* ((f (ep))
       (i0 (- (H f) 1))
       (q (+ 3 (- 1 (P f))))
       (k 4)
       (c (- (* 2 (2^{P-1} f)) k))
       (v (* c (expt 2 q)))
       (e (e v))
       (i (algo1-i i0 v f))
       (dv (algo1 i0 v f)))
  (list
   :format f
   :i0 i0
   :q q
   :k k
   :c c
   :v v
   :x #fx1.fffffffffffffff8p3
   :e e
   :signum (signum (- (expt 2 q) (expt (D) (- e i0))))
   :i i
   :dv dv)))
|#

; First part of result-3 for half-precision format (hp)
(defrule result-3-1-hp
  (let* ((f (hp))
         (v #fx1.ff8p3))
    (implies (and (posp i)
                  (< i (H f))
                  (pos-rationalp d)
                  (has-D-length d i))
             (and (finite-positive-binary-p v f)
                  (not (in-tau-intervalp d (Rv v f))))))
  :use (:instance algo1-i<=max-from-i-j
                  (from-i 1)
                  (f (hp))
                  (v #fx1.ff8p3)
                  (j i))
  :enable (hp))

; First part of result-3 for single-precision format (sp)
(defrule result-3-1-sp
  (let* ((f (sp))
         (v #fx1.fffffcp6))
    (implies (and (posp i)
                  (< i (H f))
                  (pos-rationalp d)
                  (has-D-length d i))
             (and (finite-positive-binary-p v f)
                  (not (in-tau-intervalp d (Rv v f))))))
  :use (:instance algo1-i<=max-from-i-j
                  (from-i 1)
                  (f (sp))
                  (v #fx1.fffffcp6)
                  (j i))
  :enable (sp))

; First part of result-3 for double-precision format (dp)
(defrule result-3-1-dp
  (let* ((f (dp))
         (v #fx1.fffffffffffffp0))
    (implies (and (posp i)
                  (< i (H f))
                  (pos-rationalp d)
                  (has-D-length d i))
             (and (finite-positive-binary-p v f)
                  (not (in-tau-intervalp d (Rv v f))))))
  :use (:instance algo1-i<=max-from-i-j
                  (from-i 1)
                  (f (dp))
                  (v #fx1.fffffffffffffp0)
                  (j i))
  :enable (dp))

; First part of result-3 for extended-precision format (ep)
(defrule result-3-1-ep
  (let* ((f (ep))
         (v #fx1.fffffffffffffff8p3))
    (implies (and (posp i)
                  (< i (H f))
                  (pos-rationalp d)
                  (has-D-length d i))
             (and (finite-positive-binary-p v f)
                  (not (in-tau-intervalp d (Rv v f))))))
  :use (:instance algo1-i<=max-from-i-j
                  (from-i 1)
                  (f (ep))
                  (v #fx1.fffffffffffffff8p3)
                  (j i))
  :enable (ep))

(acl2::with-arith5-help
 (defrule algo1-i<=max-from-i-H
   (<= (algo1-i from-i v f) (max (acl2::pos-fix from-i) (H f)))
   :rule-classes :linear
   :enable (u_i-linear w_i-linear)
   :use ((:instance algo1-i<=max-from-i-j
                    (d (if (in-tau-intervalp (u_i (H f) v) (Rv v f))
                           (u_i (H f) v)
                         (w_i (H f) v)))
                    (j (H f)))
         (:instance u-or-w-in-Rv
                   (u (u_i (H f) v))
                   (w (w_i (H f) v))))
   :prep-lemmas
   ((acl2::with-arith5-nonlinear++-help
     (defruled lemma1
       (< (expt (D) (- (e v) (H f))) (wid-Rv v f))
       :rule-classes :linear
       :cases ((not (< (expt (D) (+ (- (H f)) (e v)))
                       (* (expt (D) (1- (e v))) (/ 1/2 (2^{P-1} f)))))
               (not (<= (* (expt (D) (1- (e v))) (/ 1/2 (2^{P-1} f)))
                        (* (pos-rational-fix v) (/ 1/2 (2^{P-1} f)))))
               (not (<= (* (pos-rational-fix v) (/ 1/2 (2^{P-1} f)))
                        (wid-Rv v f))))
       :hints (("subgoal 3" :use (:instance H-def (n (H f))))
               ("subgoal 2" :in-theory (enable e)
                :use (:instance result-1-3
                                (x (pos-rational-fix v))
                                (k (ordD v))))
               ("subgoal 1" :in-theory (enable wid-Rv-as-c-q c)
                :use (:instance c-linear (x v))))))
    (defrule lemma2
      (< (w_i (H f) v) (+ (wid-Rv v f) (u_i (H f) v)))
      :enable (lemma1 w_i-as-u_i)))))


; Second part of result 3
(defrule result-3-2
  (implies (and (integerp i)
                (>= i (H f))
                (posp from-i)
                (>= i from-i))
           (let ((dv (algo1 from-i v f)))
             (and (has-D-length dv i)
                  (in-tau-intervalp dv (Rv v f)))))
  :use ((:instance has-D-length-monotone
                  (x (algo1 from-i v f))
                  (i (algo1-i from-i v f))
                  (j i))
        algo1-i<=max-from-i-H))

(acl2::with-arith5-help
 (define Gp
  ((p integerp))
  :returns (gp integerp :rule-classes ())
  (let* ((2^{p-1} (expt 2 (- (ifix p) 1)))
         (ordD (ordD 2^{p-1})))
    (if (= 2^{p-1} (expt (D) (- ordD 1))) (- ordD 2) (- ordD 1)))
  ///
  (fty::deffixequiv Gp)
  (defrule Gp-monotone
    (implies (<= (ifix p1) (ifix p2))
             (<= (Gp p1) (Gp p2)))
    :disable ifix
    :use ((:instance result-1-4
                     (x (expt 2 (1- (ifix p1))))
                     (y (expt 2 (1- (ifix p2)))))
          (:instance result-1-3
                     (x (expt 2 (1- (ifix p1))))
                     (k  (ordD (expt 2 (1- (ifix p2))))))))
  (acl2::with-arith5-help
   (defrule Gp-def
     (implies (integerp n)
              (equal (> (expt 2 (- (ifix p) 1)) (expt (D) n))
                     (<= n (Gp p))))
     :rule-classes ()
     :enable ((D))
     :cases ((<= n (Gp p))
             (>= n (1+ (Gp p))))
     :use (:instance result-1-3
                     (x (expt 2 (- (ifix p) 1)))
                     (k (ordD (expt 2 (- (ifix p) 1)))))))))

(acl2::with-arith5-help
 (define G
  ((f formatp))
  :returns (G natp :rule-classes :type-prescription
              :hints (("goal" :use (:instance Gp-def
                                              (n 0)
                                              (p (P f))))))
  (Gp (P f))
  ///
  (fty::deffixequiv G)
  (acl2::with-arith5-nonlinear-help
   (defrule G-def
     (implies (integerp n)
              (equal (> (2^{P-1} f) (expt (D) n))
                     (<= n (G f))))
     :rule-classes ()
     :enable 2^{P-1}
     :use (:instance Gp-def (p (P f)))))))

(rule
 (and (= (G (hp)) 3)
      (= (G (sp)) 6)
      (= (G (dp)) 15)
      (= (G (ep)) 18))
 :enable (hp sp dp ep))

(acl2::with-arith5-nonlinear++-help
 (defrule MIN_NORMAL-lemma
  (implies (and (pos-rationalp v)
                (<= (MIN_NORMAL f) v))
           (>= (* v (/ (2^{P-1} f)))
               (expt 2 (q v f))))
  :enable c
  :use (:instance c-vs-MIN_NORMAL (x v))))

(acl2::with-arith5-nonlinear++-help
 (defruled ulps-when-c>=2^{p-1}
  (implies (and (>= (c v f) (expt 2 (- (ifix p) 1)))
                (integerp i)
                (<= i (Gp p)))
           (< (expt 2 (q v f))
              (expt (D) (- (e v) i))))
  :enable (e c)
  :use ((:instance Gp-def
                   (n i))
        (:instance result-1-3
                   (x v)
                   (k (ordD v))))))
#|
(acl2::with-arith5-nonlinear++-help
 (defruled ulps-when-i<=G-and-normal
   (implies (and (posp i)
                 (<= i (G f))
                 (<= (MIN_NORMAL f) (pos-rational-fix v)))
            (< (expt 2 (q v f))
               (expt (D) (- (e v) i))))
   :enable (c 2^{P-1} G)
   :use ((:instance ulps-when-c>=2^p
                    (p (P f)))
         (:instance MIN_NORMAL-lemma
                    (v (pos-rational-fix v))))))
|#
(acl2::with-arith5-nonlinear-help
 (defruled at-most-one-above-when-c>=2^{p-1}
  (implies (and (< (w_i i v) d)
                (>= (c v f) (expt 2 (- (ifix p) 1)))
                (<= (acl2::pos-fix i) (Gp p))
                (pos-rationalp d)
                (has-D-length d i))
           (not (in-tau-intervalp d (Rv v f))))
  :enable (in-tau-intervalp-Rv w_i-linear e)
  :use ((:instance lemma
                   (i (acl2::pos-fix i))
                   (w (w_i i v)))
        (:instance ulps-when-c>=2^{p-1}
                   (i (acl2::pos-fix i)))
        (:instance result-1-4
                   (x v)
                   (y (w_i i v))))
  :prep-lemmas
  ((defrule vr-alt
     (equal (vr v f)
            (+ (pos-rational-fix v) (* 1/2 (expt 2 (q v f)))))
     :enable (vr c))
   (defruled lemma
     (implies (and (pos-rationalp w)
                   (pos-rationalp d)
                   (posp i)
                   (has-D-length w i)
                   (has-D-length d i)
                   (< w d))
              (<= (+ w (expt (D) (- (e w) i))) d))
     :enable (has-D-length-as-exactrp e-as-expe expq)
     :use (:instance fpr+2
                     (b (D))
                     (p i)
                     (x w)
                     (y d))))))
#|
(acl2::with-arith5-nonlinear++-help
 (defruled at-most-one-above-when-i<=G-and-normal
  (implies (and (< (w_i i v) d)
                (<= (acl2::pos-fix i) (G f))
                (<= (MIN_NORMAL f) (pos-rational-fix v))
                (pos-rationalp d)
                (has-D-length d i))
           (not (in-tau-intervalp d (Rv v f))))
   :enable (c 2^{P-1} G)
   :use ((:instance at-most-one-above-when-c>=2^{p-1}
                    (p (P f)))
         (:instance MIN_NORMAL-lemma
                    (v (pos-rational-fix v))))))
|#
(acl2::with-arith5-nonlinear-help
 (defruled at-most-one-below-when-c>=2^{p-1}
  (implies (and (< D (u_i i v))
                (>= (c v f) (expt 2 (- (ifix p) 1)))
                (<= (acl2::pos-fix i) (Gp p))
                (pos-rationalp d)
                (has-D-length d i))
           (not (in-tau-intervalp d (Rv v f))))
  :enable (in-tau-intervalp-Rv u_i-linear)
  :cases ((= (u_i i v) (expt (D) (1- (e (u_i i v))))))
  :use ((:instance lemma
                   (i (acl2::pos-fix i))
                   (u (u_i i v)))
        vl-alt-2)
  :hints (("subgoal 2" :use lemma2)
          ("subgoal 1" :use (:instance lemma1
                                       (p (ifix p)))))
  :prep-lemmas
  ((acl2::with-arith5-help
    (defruled vl-alt-2
      (>= (vl v f)
          (- (pos-rational-fix v) (* 1/2 (expt 2 (q v f)))))
      :enable (vl c)))
   (acl2::with-arith5-help
    (defruled lemma0
      (< (* 1/2 (pos-rational-fix v)) (u_i i v))
      :cases ((<= (w_i i v) (* 2 (u_i i v))))
      :hints (("subgoal 2" :in-theory (enable u_i w_i t_i))
              ("subgoal 1" :in-theory (enable w_i-linear)))))
   (acl2::with-arith5-nonlinear++-help
    (defruled lemma1
      (implies (and (>= (c v f) (expt 2 (- (ifix p) 1)))
                    (<= (acl2::pos-fix i) (Gp p))
                    (integerp p)
                    (= (u_i i v) (expt (D) (1- (e (u_i i v))))))
               (< (expt 2 (- (q v f) 1))
                  (expt (D) (+ -1 (- (acl2::pos-fix i)) (e (u_i i v))))))
      :cases ((not (<= (expt 2 (- (q v f) 1))
                       (* (pos-rational-fix v) (expt 2 (- p)))))
              (not (<  (* (pos-rational-fix v) (expt 2 (- p)))
                       (* (pos-rational-fix (u_i i v)) (expt 2 (- 1 p)))))
              (not (=  (* (pos-rational-fix (u_i i v)) (expt 2 (- 1 p)))
                       (* (expt (D) (1- (e v))) (expt 2 (- 1 p)))))
              (not (<  (* (expt (D) (1- (e v))) (expt 2 (- 1 p)))
                       (expt (D) (+ -1 (- (acl2::pos-fix i)) (e v)))))
              (not (=  (expt (D) (+ -1 (- (acl2::pos-fix i)) (e v)))
                       (expt (D) (+ -1 (- (acl2::pos-fix i)) (e (u_i i v)))))))
      :hints
      (("subgoal 5" :in-theory (enable c))
       ("subgoal 4" :use (:instance lemma0))
       ("subgoal 3" :in-theory (enable e))
       ("subgoal 2" :use (:instance Gp-def
                                    (n (acl2::pos-fix i))))
       ("subgoal 1" :in-theory (enable e)))))
   (acl2::with-arith5-nonlinear-help
    (defruled lemma2
      (implies (and (>= (c v f) (expt 2 (- (ifix p) 1)))
                    (<= (acl2::pos-fix i) (Gp p)))
               (< (* 1/2 (expt 2 (q v f)))
                  (expt (D) (+ (- (acl2::pos-fix i)) (e (u_i i v))))))
      :enable (e u_i-linear)
      :use ((:instance ulps-when-c>=2^{p-1}
                       (i (acl2::pos-fix i))))))
   (defruled lemma
     (implies (and (pos-rationalp u)
                   (pos-rationalp d)
                   (posp i)
                   (has-D-length u i)
                   (has-D-length d i)
                   (< d u))
              (let ((e (if (= u (expt (D) (1- (e u))))
                           (- (e u) 1)
                         (e u))))
                (<= d (- u (expt (D) (- e i))))))
     :enable (has-D-length-as-exactrp e-as-expe expq)
     :use (:instance fpr-2
                     (b (D))
                     (p i)
                     (x u)
                     (y d))))))
#|
(acl2::with-arith5-nonlinear++-help
 (defruled at-most-one-below-when-i<=G-and-normal
   (implies (and (< D (u_i i v))
                 (<= (acl2::pos-fix i) (G f))
                 (<= (MIN_NORMAL f) (pos-rational-fix v))
                 (pos-rationalp d)
                 (has-D-length d i))
            (not (in-tau-intervalp d (Rv v f))))
   :enable (c 2^{P-1} G)
   :use ((:instance at-most-one-below-when-c>=2^{p-1}
                    (p (P f)))
         (:instance MIN_NORMAL-lemma
                    (v (pos-rational-fix v))))))
|#
(defrule may-contain-only-u_i-or-W-i-when-c>=2^{p-1}
  (implies (and (>= (c v f) (expt 2 (- (ifix p) 1)))
                (<= (acl2::pos-fix i) (Gp p))
                (pos-rationalp d)
                (has-D-length d i)
                (in-tau-intervalp d (Rv v f)))
           (or (equal d (u_i i v))
               (equal d (w_i i v))))
  :rule-classes ()
  :enable (u_i-linear w_i-linear)
  :hints (("subgoal 2" :use at-most-one-below-when-c>=2^{p-1})
          ("subgoal 1" :use at-most-one-above-when-c>=2^{p-1}))
  :use uninteresting-other-than-u_i-w_i
  :cases ((< d (u_i i v)) (> d (w_i i v))))
#|
(acl2::with-arith5-nonlinear++-help
 (defrule may-contain-only-u_i-or-W-i-when-i<=G-and-normal
 (implies (and (<= (acl2::pos-fix i) (G f))
               (<= (MIN_NORMAL f) (pos-rational-fix v))
               (pos-rationalp d)
               (has-D-length d i)
               (in-tau-intervalp d (Rv v f)))
          (or (equal d (u_i i v))
              (equal d (w_i i v))))
 :enable (c 2^{P-1} G)
 :use ((:instance may-contain-only-u_i-or-W-i-when-c>=2^{p-1}
                  (p (P f)))
       (:instance MIN_NORMAL-lemma
                  (v (pos-rational-fix v))))))
|#
(defrule result-4-part-1-when-c>=2^{p-1}
   (implies (and (posp i)
                 (>= (c v f) (expt 2 (- (ifix p) 1)))
                 (<= i (Gp p))
                 (pos-rationalp v)
                 (pos-rationalp d1)
                 (has-D-length d1 i)
                 (in-tau-intervalp d1 (Rv v f))
                 (pos-rationalp d2)
                 (has-D-length d2 i)
                 (not (= d1 d2)))
            (not (in-tau-intervalp d2 (Rv v f))))
   :enable (wid-Rv-as-c-q w_i-as-u_i)
   :use ((:instance may-contain-only-u_i-or-W-i-when-c>=2^{p-1}
                    (d d1))
         (:instance may-contain-only-u_i-or-W-i-when-c>=2^{p-1}
                    (d d2))
         (:instance ulps-when-c>=2^{p-1})
         (:instance at-most-one-in-Rv
                    (u (u_i i v))
                    (w (w_i i v)))))

; First part of result 4
; Hypotheis v >= MIN_NORMAL is weaker than in the paper
(acl2::with-arith5-nonlinear++-help
 (defrule result-4-part-1
   (implies (and (posp i)
                 (<= i (G f))
                 (pos-rationalp v)
                 (>= v (MIN_NORMAL f))
                 (pos-rationalp d1)
                 (has-D-length d1 i)
                 (in-tau-intervalp d1 (Rv v f))
                 (pos-rationalp d2)
                 (has-D-length d2 i)
                 (not (= d1 d2)))
            (not (in-tau-intervalp d2 (Rv v f))))
   :enable (c 2^{P-1} G)
   :use ((:instance result-4-part-1-when-c>=2^{p-1}
                    (p (P f)))
         MIN_NORMAL-lemma)))

; Counterexample for second part of result 4
; No decimals of length G+1 in the rounding interval of this v
(rule
 (let* ((f (dp))
        (i (+ (G f) 1))
        (v #fx1.0000000000001p0))
   (and (finite-positive-binary-p v f)
        (> v (MIN_NORMAL f))
        (implies (and (pos-rationalp d)
                      (has-D-length d i))
                 (not (in-tau-intervalp d (Rv v f))))))
 :use (:instance uninteresting-other-than-u_i-w_i
                 (f (dp))
                 (i (+ (G (dp)) 1))
                 (v #fx1.0000000000001p0))
 :enable dp)
