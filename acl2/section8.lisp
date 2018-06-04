#|
(include-book "rtl/rel11/portcullis" :dir :system)
|#
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
              :hints (("goal" :use (:instance expe>=
                                              (b (D))
                                              (x (* 2 (2^{P-1} f)))
                                              (n 0)))))
  (+ (expe (* 2 (2^{P-1} f)) (D)) 2)
  ///
  (fty::deffixequiv H)
  (acl2::with-arith5-help
   (defrule H-def
     (implies (integerp n)
              (equal (> (expt (D) (- n 1)) (* 2 (2^{P-1} f)))
                     (>= n (H f))))
     :rule-classes ()
     :cases ((>= n (H f))
             (<= n (1- (H f))))
     :hints (("subgoal 2" :use (:instance expe>=
                                          (b (D))
                                          (n (1- n))
                                          (x (* 2 (2^{P-1} f)))))
             ("subgoal 1" :use (:instance expe<=
                                          (b (D))
                                          (n (- n 2))
                                          (x (* 2 (2^{P-1} f)))))))))

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

(defrule result-3-incorrect-for-artificalformat
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
(defrule result-3-hp
  (let* ((f (hp))
         (v #fx1.ff8p3))
    (implies (and (posp i)
                  (< i (H f))
                  (pos-rationalp d)
                  (has-D-length d i))
             (and (finite-positive-binary-p v f)
                  (not (in-tau-intervalp d (Rv v f))))))
  :use (:instance i<=max-from-j-algo1
                  (from 1)
                  (f (hp))
                  (v #fx1.ff8p3)
                  (j i))
  :enable (hp))

; First part of result-3 for single-precision format (sp)
(defrule result-3-sp
  (let* ((f (sp))
         (v #fx1.fffffcp6))
    (implies (and (posp i)
                  (< i (H f))
                  (pos-rationalp d)
                  (has-D-length d i))
             (and (finite-positive-binary-p v f)
                  (not (in-tau-intervalp d (Rv v f))))))
  :use (:instance i<=max-from-j-algo1
                  (from 1)
                  (f (sp))
                  (v #fx1.fffffcp6)
                  (j i))
  :enable (sp))

; First part of result-3 for double-precision format (dp)
(defrule result-3-dp
  (let* ((f (dp))
         (v #fx1.fffffffffffffp0))
    (implies (and (posp i)
                  (< i (H f))
                  (pos-rationalp d)
                  (has-D-length d i))
             (and (finite-positive-binary-p v f)
                  (not (in-tau-intervalp d (Rv v f))))))
  :use (:instance i<=max-from-j-algo1
                  (from 1)
                  (f (dp))
                  (v #fx1.fffffffffffffp0)
                  (j i))
  :enable (dp))

; First part of result-3 for extended-precision format (ep)
(defrule result-3-ep
  (let* ((f (ep))
         (v #fx1.fffffffffffffff8p3))
    (implies (and (posp i)
                  (< i (H f))
                  (pos-rationalp d)
                  (has-D-length d i))
             (and (finite-positive-binary-p v f)
                  (not (in-tau-intervalp d (Rv v f))))))
  :use (:instance i<=max-from-j-algo1
                  (from 1)
                  (f (ep))
                  (v #fx1.fffffffffffffff8p3)
                  (j i))
  :enable (ep))

; Second part of result 3
(defrule result-3
  (implies (and (integerp i)
                (>= i (H f))
                (finite-positive-binary-p v f))
           (let ((dv (algo1 i v f)))
             (and (has-D-length dv i)
                  (in-tau-intervalp dv (Rv v f)))))
  :enable algo1-is-u_i-or-w_i
  :cases ((= (algo1 i v f) (u_i i v))
          (= (algo1 i v f) (w_i i v)))
  :prep-lemmas
  ((acl2::with-arith5-nonlinear++-help
    (defrule lemma0
     (implies (and (integerp i)
                   (>= i (H f)))
              (< (expt (D) (+ (- i) (e v))) (wid-Rv v f)))
     :cases ((not (< (expt (D) (+ (- i) (e v)))
                     (* (expt (D) (1- (e v))) (/ 1/2 (2^{P-1} f)))))
             (not (<= (* (expt (D) (1- (e v))) (/ 1/2 (2^{P-1} f)))
                      (* (pos-rational-fix v) (/ 1/2 (2^{P-1} f)))))
             (not (<= (* (pos-rational-fix v) (/ 1/2 (2^{P-1} f)))
                      (wid-Rv v f))))
     :hints (("subgoal 3" :use (:instance H-def (n i)))
             ("subgoal 2" :in-theory (enable e)
              :use (:instance result-1-3
                      (x (pos-rational-fix v))
                      (k (ordD v))))
             ("subgoal 1" :in-theory (enable wid-Rv-as-c-q c)
              :use (:instance c-linear (x v))))))
   (acl2::with-arith5-help
    (defrule lemma
     (implies (and (integerp i)
                   (>= i (H f)))
              (equal (algo1-i i v f) i))
     :enable (u_i-linear w_i-linear algo1-i
                         w_i-as-u_i)
     :use (:instance u-or-w-in-Rv
                     (u (u_i i v))
                     (w (w_i i v)))))))

#|
(define G
  ((f formatp))
  :returns (H natp :rule-classes :type-prescription
              :hints (("goal" :use (:instance expe>=
                                              (b (D))
                                              (x (* 2 (2^{P-1} f)))
                                              (n 0)))))
  (let ((ordD (ordD (2^{P-1} f))))
    (if (= (w^{P-1} f) (expt (D) ordD)) (- ordD
  (+ (expe (* 2 (2^{P-1} f)) (D)) 2)
  ///
  (fty::deffixequiv H)
  (acl2::with-arith5-help
   (defrule H-def
     (implies (integerp n)
              (equal (> (expt (D) (- n 1)) (* 2 (2^{P-1} f)))
                     (>= n (H f))))
     :rule-classes ()
     :cases ((>= n (H f))
             (<= n (1- (H f))))
     :hints (("subgoal 2" :use (:instance expe>=
                                          (b (D))
                                          (n (1- n))
                                          (x (* 2 (2^{P-1} f)))))
             ("subgoal 1" :use (:instance expe<=
                                          (b (D))
                                          (n (- n 2))
                                          (x (* 2 (2^{P-1} f)))))))))

(rule
 (and (= (H (hp)) 5)
      (= (H (sp)) 9)
      (= (H (dp)) 17)
      (= (H (ep)) 21))
 :enable (hp sp dp ep))
|#
