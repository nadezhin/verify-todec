(in-package "RTL")
(include-book "std/util/defrule" :dir :system)
(include-book "rtl/rel11/support/reps" :dir :system)
(include-book "tools/with-arith5-help" :dir :system)

(local (include-book "rtl/rel11/support/verify-guards" :dir :system))
(local (include-book "rtl/rel11/support/bits" :dir :system))
(local (include-book "rtl/rel11/support/float" :dir :system))
(local (acl2::allow-arith5-help))

(defrule expt-natp
  (implies (natp i)
           (posp (expt 2 i)))
  :rule-classes :type-prescription)

(defrule expw-type
  (implies (formatp f)
           (and (integerp (expw f))
                (<= 2 (expw f))))
  :rule-classes :type-prescription
  :enable (formatp expw))

(defrule prec-type
  (implies (formatp f)
           (and (integerp (prec f))
                (<= 2 (prec f))))
  :rule-classes :type-prescription
  :enable (formatp prec))

(defrule sgnf-type
  (bitp (sgnf x f))
  :rule-classes :type-prescription
  :enable sgnf)

(rule
 (let ((f '(nil w -1)))
   (equal (bias f) -3/4)))

(defrule expf-linear
  (implies (formatp f)
           (<= (expf x f) (1+ (* 2 (bias f)))))
  :rule-classes :linear
  :enable (expf bias)
  :use (:instance bits-bounds
                  (i (+ -1 (expw f) (sigw f)))
                  (j (sigw f))))

(defruled expf-0
  (implies (encodingp x f)
           (equal (equal (expf x f) 0)
                  (or (zerp x f)
                      (denormp x f)
                      (pseudop x f))))
  :enable (zerp denormp pseudop)
  :rule-classes
  (:rewrite
   (:rewrite :corollary (implies (zerp x f) (equal (expf x f) 0)))
   (:rewrite :corollary (implies (denormp x f) (equal (expf x f) 0)))
   (:rewrite :corollary (implies (pseudop x f) (equal (expf x f) 0)))))

(defrule expf-when-normp
  (implies (normp x f)
           (and (<= 1 (expf x f))
                (<= (expf x f) (* 2 (bias f)))))
  :rule-classes :linear
  :enable (normp encodingp bias))

(defrule expf-when-infp
  (implies (infp x f)
           (equal (expf x f) (1+ (* 2 (bias f)))))
  :enable (infp bias))

(defrule manf-linear
  (implies (formatp f)
           (< (manf x f) (expt 2 (1- (prec f)))))
  :rule-classes :linear
  :enable manf
  :use (:instance bits-bounds
                  (i (+ -2 (prec f)))
                  (j 0)))

(defrule sigf-as-manf
  (implies (formatp f)
           (equal (sigf x f)
                  (if (and (explicitp f)
                           (= (bitn x (1- (prec f))) 1))
                      (+ (expt 2 (1- (prec f))) (manf x f))
                    (manf x f))))
  :enable (sigf manf sigw)
  :use (:instance bitn-plus-bits
                  (m 0)
                  (n (1- (prec f)))))

(acl2::with-arith5-help
 (defruled signum-decode
  (implies (formatp f)
           (equal (signum (decode x f))
                  (if (and (= (expf x f) 0)
                           (= (manf x f) 0)
                           (implies (explicitp f)
                                    (equal (bitn x (1- (prec f))) 0)))
                      0
                    (if (= (sgnf x f) 1) -1 1))))
  :enable (signum decode ndecode ddecode)))

(acl2::with-arith5-help
 (defrule expo-decode
   (implies
    (formatp f)
    (equal
     (expo (decode x f))
     (cond ((not (= (expf x f) 0)) (- (expf x f) (bias f)))
           ((and (explicitp f)
                 (equal (bitn x (1- (prec f))) 1))
            (- 1 (bias f)))
           ((= (manf x f) 0) 0)
           (t (+ (expo (manf x f)) (- 2 (+ (bias f) (prec f))))))))
   :enable (decode ndecode ddecode)
   :use (:instance
         expo-unique
         (x (decode x f))
         (n (cond ((not (= (expf x f) 0)) (- (expf x f) (bias f)))
                  ((and (explicitp f)
                        (equal (bitn x (1- (prec f))) 1))
                   (- 1 (bias f)))
                  ((= (manf x f) 0) 0)
                  (t (+ (expo (manf x f)) (- 2 (+ (bias f) (prec f))))))))
    :prep-lemmas
    ((acl2::with-arith5-nonlinear-help
      (defrule lemma
        (implies (formatp f)
                 (< (* (expt 2 (- 1 (prec f))) (manf x f)) 1))))
     (defrule expo-shift-alt
      (implies (and (rationalp x)
                    (not (equal x 0))
                    (integerp n))
               (equal (expo (* x (expt 2 n)))
                      (+ n (expo x))))
      :use expo-shift))))

(acl2::with-arith5-help
 (defrule sig-decode
   (implies
    (formatp f)
    (equal (sig (decode x f))
           (if (or (not (= (expf x f) 0))
                   (and (explicitp f)
                        (equal (bitn x (1- (prec f))) 1)))
               (1+ (* (manf x f) (expt 2 (- 1 (prec f)))))
             (sig (manf x f)))))
   :enable (sig signum)
   :disable abs
   :use (:instance signum-decode)
   :prep-lemmas
   ((defrule open-ndecode
      (implies (and (formatp f)
                    (not (= (expf x f) 0)))
               (equal (* (decode x f) (expt 2 (- (bias f) (expf x f))))
                      (* (signum (decode x f))
                         (1+ (* (manf x f) (expt 2 (- 1 (prec f))))))))
      :enable (decode ndecode signum))
    (defrule open-ddecode
      (implies (and (formatp f)
                    (= (expf x f) 0))
               (equal (* (decode x f) (expt 2 (+ -2 (bias f) (prec f))))
                      (* (signum (decode x f))
                         (sigf x f))))
      :enable (decode ddecode signum))
    (defrule open-pseudo
      (implies (and (formatp f)
                    (= (expf x f) 0)
                    (explicitp f)
                    (= (bitn x (1- (prec f))) 1))
               (equal (* (expt 2 (1- (bias f))) (decode x f))
                      (* (signum (decode x f))
                         (1+ (* (manf x f) (expt 2 (- 1 (prec f))))))))
      :enable (decode ddecode signum)))))

(defrule decode-0
  (implies (encodingp x f)
           (equal (equal (decode x f) 0)
                  (zerp x f))))

(defrule drepp-decode
  (implies (encodingp x f)
           (equal (drepp (decode x f) f)
                  (denormp x f)))
  :cases ((drepp (decode x f) f))
  :hints (("subgoal 2" :in-theory (enable decode))
          ("subgoal 1" :in-theory (enable drepp denormp))))

(defrule expf-when-nanp
  (implies (nanp x f)
           (equal (expf x f) (1+ (* 2 (bias f)))))
  :enable (nanp bias))

(defrule sigf-linear
  (implies (formatp f)
           (< (sigf x f) (expt 2 (sigw f))))
  :rule-classes :linear
  :enable sigf
  :use (:instance bits-bounds
                  (i (+ -1 (sigw f)))
                  (j 0)))

(defrule sig-subnormal-type
  (implies (denormp x f)
           (posp (sigf x f)))
  :rule-classes :type-prescription
  :enable denormp)

(acl2::with-arith5-help
 (defrule sigf-subnormal-linear
   (implies (denormp x f)
            (< (sigf x f) (expt 2 (- (prec f) 1))))
   :rule-classes :linear
   :enable (denormp encodingp sigf sigw)
   :cases ((explicitp f))
   :hints (("subgoal 2" :use sigf-linear)
           ("subgoal 1" :use ((:instance bitn-plus-bits
                                         (m 0)
                                         (n (1- (prec f))))
                              (:instance bits-bounds
                                         (i (+ -2 (prec f)))
                                         (j 0)))))))

(defrule sigf-pseudop-linear
  (implies (pseudop x f)
           (<= (expt 2 (- (prec f) 1)) (sigf x f)))
  :rule-classes :linear
  :enable (pseudop encodingp sigf sigw)
  :use (:instance bitn-plus-bits
                  (m 0)
                  (n (1- (prec f)))))

(defrule sigf-zerp
  (implies (zerp x f)
           (equal (sigf x f) 0))
  :enable zerp)

(defrule manf-linear
  (implies (formatp f)
           (< (manf x f) (expt 2 (1- (prec f)))))
  :rule-classes :linear
  :enable manf
  :use (:instance bits-bounds
                  (i (+ -2 (prec f)))
                  (j 0)))

(defrule decode-zerp
  (implies (zerp x f)
           (equal (decode x f) 0))
  :enable decode-0)

(defrule decode-denormp
  (implies (denormp x f)
           (drepp (decode x f) f))
  :enable decode)

(acl2::with-arith5-help
 (defrule decode-pseudop
  (implies (pseudop x f)
           (nrepp (decode x f) f))
  :enable (pseudop nrepp exactp)
  :use signum-decode))
