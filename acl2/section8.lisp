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

; First part of result-3 is not true for *format-for-result-3*
; For all finite-positive-binary v of this format algo1 returns
; decimal of length H-1 which is rounded back to v

(defconst *format-for-result-3* '(nil 4 2))

(rule
 (and (formatp *format-for-result-3*)
      (= (P *format-for-result-3*) 4)
      (= (W_ *format-for-result-3*) 2)
      (= (H *format-for-result-3*) 3)
      (= (Qmin *format-for-result-3*) -3)
      (= (Qmax *format-for-result-3*) -2)))

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

#|
; Engine to search v for first part of result-3
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
#|
; Second part of result 3
(defrule result-3
  (implies (and (integerp i)
                (>= i (H f))
                (finite-positive-binary-p v f))
           (let ((dv (algo1 i v f)))
             (and (has-D-length dv i)
                  (in-tau-intervalp dv (Rv v f)))))
  :prep-lemmas
  ((acl2::with-arith5-help
    (defrule lemma
     (implies (and (integerp i)
                   (>= i (H f)))
              (equal (algo1-i i v f) i))
;     :enable w_i-as-u_i
     :enable (u_i-linear w_i-linear width-Rv w_i-as-u_i)
     :use ((:instance H-def (n i))
           (:instance u-or-w-in-Rv
                      (u (u_i i v))
                      (w (w_i i v))))
     :expand (algo1-i i v f)
     )
   ))
  )
|#
