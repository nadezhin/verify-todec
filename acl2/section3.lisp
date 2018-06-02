(in-package "RTL")
(include-book "section2")

(local (include-book "rtl/rel11/support/bits" :dir :system))
(local (include-book "rtl/rel11/support/float" :dir :system))
(local (include-book "rtl/rel11/support/reps" :dir :system))
(local (include-book "reps-lemmas"))
(local (acl2::allow-arith5-help))

; Section 3 of the paper

(define P
  ((f formatp "Floating point format"))
  :returns (P (and (integerp P) (< 1 P))
              :rule-classes :type-prescription)
  (prec (format-fix f))
  ///
  (fty::deffixequiv P))

(acl2::with-arith5-help
 (define 2^{P-1}
   ((f formatp "Floating point format"))
   :returns (2^{P-1} (and (integerp 2^{P-1}) (< 1 2^{P-1}))
                     :rule-classes :type-prescription)
   (expt 2 (- (P f) 1))
   ///
   (fty::deffixequiv 2^{P-1})))

(define W_
  ((f formatp "Floating point format"))
  :returns (W (and (integerp w) (< 1 w))
              :rule-classes :type-prescription)
  (expw (format-fix f))
  ///
  (fty::deffixequiv W_))

(acl2::with-arith5-help
 (define 2^{W-1}
   ((f formatp "Floating point format"))
   :returns (2^{W-1} (and (integerp 2^{W-1}) (< 1 2^{W-1}))
                     :rule-classes :type-prescription)
   (expt 2 (- (W_ f) 1))
   ///
   (fty::deffixequiv 2^{W-1})
   (defruled 2^{W-1}-as-bias
     (equal (2^{W-1} f)
            (1+ (bias (format-fix f))))
     :enable (W_ bias))))

(define Qmin
  ((f formatp "Floating point format"))
  :returns (qmin integerp :rule-classes ())
  (+ (- (2^{W-1} f)) (- (P f)) 3)
  ///
  (fty::deffixequiv Qmin))

(define Qmax
  ((f formatp "Floating point format"))
  :returns (qmin integerp :rule-classes ())
  (- (2^{W-1} f) (P f))
  ///
  (fty::deffixequiv Qmax)
  (defruled Qmax-as-Qmin
    (equal (Qmax f)
           (+ (Qmin f) (* 2 (2^{W-1} f)) -3))
    :enable Qmin))

(define Cmax
  ((f formatp))
  :returns (Cmax (and (integerp Cmax) (< 1 Cmax))
                 :rule-classes :type-prescription)
  (- (* 2 (2^{P-1} f)) 1)
  ///
  (fty::deffixequiv Cmax)
  (defrule Cmax-linear
    (<= 3 (Cmax f))
    :rule-classes :linear))

(acl2::with-arith5-help
 (define MIN_VALUE
   ((f formatp "Floating point format"))
   :returns (v pos-rationalp :rule-classes ())
   (expt 2 (Qmin f))
   ///
   (fty::deffixequiv MIN_VALUE)
   (defruled MIN_VALUE-as-spd
     (equal (MIN_VALUE f)
            (spd (format-fix f)))
     :enable (Qmin P 2^{W-1}-as-bias spd))))

(acl2::with-arith5-help
 (define MIN_NORMAL
   ((f formatp "Floating point format"))
   :returns (v pos-rationalp :rule-classes ()
               :hints (("goal" :in-theory (enable Qmin 2^{P-1}))))
   (* (2^{P-1} f) (expt 2 (Qmin f)))
   ///
   (fty::deffixequiv MIN_NORMAL)
   (defruled MIN_NORMAL-alt
     (equal (MIN_NORMAL f)
            (expt 2 (- 2 (2^{W-1} f))))
     :rule-classes :definition
     :enable (Qmin 2^{P-1}))
   (defruled MIN_NORMAL-as-spn
     (equal (MIN_NORMAL f)
            (spn (format-fix f)))
     :enable (Qmin 2^{P-1} 2^{W-1}-as-bias spn))))

(acl2::with-arith5-help
 (define MAX_VALUE
  ((f formatp "Floating point format"))
  :returns (v pos-rationalp :rule-classes ())
  (* (Cmax f) (expt 2 (Qmax f)))
  ///
  (fty::deffixequiv MAX_VALUE)
  (acl2::with-arith5-help
   (defruled MAX_VALUE-as-lpn
     (equal (MAX_VALUE f)
            (lpn (format-fix f)))
     :enable (Qmax Cmax 2^{W-1}-as-bias 2^{P-1} P lpn bias)))))

(defruled float-constants
  (let ((f (sp)))
    (and (equal (P f) 24)
         (equal (W_ f) 8)
         (equal (bias f) 127)
         (equal (Qmin f) -149)
         (equal (Qmax f) 104)
         (equal (Cmax f) #xffffff)
         (equal (MIN_VALUE f) #fx1p-149)
         (equal (MIN_NORMAL f) #fx1p-126)
         (equal (MAX_VALUE f) #fx1.fffffep127)))
  :enable ((sp)))

(defruled double-constants
  (let ((f (dp)))
    (and (equal (P f) 53)
         (equal (W_ f) 11)
         (equal (bias f) 1023)
         (equal (Qmin f) -1074)
         (equal (Qmax f) 971)
         (equal (Cmax f) #x1fffffffffffff)
         (equal (MIN_VALUE f) #fx1p-1074)
         (equal (MIN_NORMAL f) #fx1p-1022)
         (equal (MAX_VALUE f) #fx1.fffffffffffffp1023)))
 :enable ((dp)))

(defruledl expo-as-expe
  (equal (expo x)
         (if (rationalp x) (expe x 2) 0))
  :enable (expo expe))

(define q
  ((x pos-rationalp)
   (f formatp))
  :returns (q integerp :rule-classes ())
  (max (Qmin f)
       (expq (pos-rational-fix x) (P f) 2))
  ///
  (fty::deffixequiv q)
  (defruled q-as-expe
    (equal (q x f)
           (let ((x (pos-rational-fix x))
                 (f (format-fix f)))
             (- (max (- 1 (bias f)) (expe x 2))
                (1- (prec f)))))
    :enable (Qmin P 2^{W-1}-as-bias expq))
  (defrule q-linear
    (<= (Qmin f) (q x f))
    :rule-classes :linear))

(defrule q-when-drepp
  (implies (and (drepp x f)
                (< 0 x))
           (equal (q x f) (Qmin f)))
  :enable (drepp q expq expo-as-expe Qmin P 2^{W-1}-as-bias))

(defrule q-when-nrepp
  (implies (nrepp x f)
           (<= (q x f) (Qmax f)))
  :rule-classes :linear
  :enable (pos-rational-fix
           nrepp q expq expo-as-expe Qmin Qmax P 2^{W-1}-as-bias bias))

(acl2::with-arith5-help
 (define c
  ((x pos-rationalp)
   (f formatp))
  :returns (c pos-rationalp :rule-classes ())
  (* (pos-rational-fix x) (expt 2 (- (q x f))))
  ///
  (fty::deffixequiv c)
  (defruled c-as-sigc
    (equal (c x f)
           (let ((x (pos-rational-fix x)))
             (if (<= (Qmin f) (expq x (P f) 2))
                 (sigc x (P f) 2)
               (* x (expt 2 (- (Qmin f)))))))
    :enable (sigc q expq sigm spd Qmin P 2^{W-1}-as-bias))))

(acl2::with-arith5-nonlinear-help
 (defrule c-linear
   (< (c x f) (* 2 (2^{P-1} f)))
  :rule-classes :linear
  :enable (c-as-sigc sigc-upper-bound Qmin 2^{P-1} expq)
  :cases ((< (c x f) (* 2 (2^{P-1} f))))
  :use (:instance expe>=
                  (b 2)
                  (x (pos-rational-fix x))
                  (n (- 2 (2^{W-1} f))))))

(acl2::with-arith5-help
 (defrule c-type-when-drepp
   (implies (drepp x f)
            (posp (c x f)))
   :rule-classes :type-prescription
   :cases ((pos-rationalp x))
   :hints (("subgoal 2" :in-theory (enable sigc pos-rational-fix)))
   :enable (drepp exactp expo-as-expe c-as-sigc spd sig
            Qmin 2^{W-1}-as-bias P expq)))

(acl2::with-arith5-nonlinear-help
 (defrule c-linear-when-drepp
   (implies (and (drepp x f)
                 (< 0 x))
            (< (c x f) (2^{P-1} f)))
  :rule-classes :linear
  :enable (drepp expo-as-expe c-as-sigc Qmin
           2^{W-1}-as-bias 2^{P-1} expq)
  :use (:instance expe>=
                  (b 2)
                  (x (pos-rational-fix x))
                  (n (- 2 (2^{W-1} f))))))

(defrule c-lower-bound-when-nrepp
  (implies (nrepp x f)
           (<= (2^{P-1} f) (c x f)))
  :rule-classes :linear
  :enable (pos-rational-fix
           nrepp expo-as-expe sigc-lower-bound Qmin 2^{P-1}
           2^{W-1}-as-bias c-as-sigc expq bias))

(acl2::with-arith5-nonlinear-help
 (defrule c-type-when-nrepp
  (implies (nrepp x f)
           (and (integerp (c x f)) (< 1 (c x f))))
  :rule-classes :type-prescription
  :use c-lower-bound-when-nrepp
  :enable (pos-rational-fix
           Qmin P 2^{W-1}-as-bias
           c-as-sigc sigc sigm sig
           nrepp exactp q ordD
           expo-as-expe bias expq)))

(defrule c-upper-bound-when-nrepp
  (implies (nrepp x f)
           (<= (c x f) (Cmax f)))
  :rule-classes :linear
  :enable Cmax)

(acl2::with-arith5-help
 (defruled unique-c*2^q
  (let ((x (* c (expt 2 q))))
    (implies (and (integerp q)
                  (<= (Qmin f) q)
                  (pos-rationalp c)
                  (or (and (<= (2^{P-1} f) c)
                           (< c (* 2 (2^{P-1} f))))
                      (and (<= 0 c)
                           (< c (2^{P-1} f))
                           (= q (Qmin f)))))
             (and (equal (q x f) q)
                  (equal (c x f) c))))
  :cases ((<= (2^{P-1} f) c))
  :enable (2^{P-1} c q ordD expq)
  :hints
  (("subgoal 2" :use ((:instance expe-shift
                                 (b 2)
                                 (x c)
                                 (n q))
                      (:instance expe<=
                                 (b 2)
                                 (x c)
                                 (n (- (P f) 2)))))
   ("subgoal 1" :use (:instance fp-rep-qc-unique
                                (b 2)
                                (p (P f))
                                (x (* c (expt 2 q))))))))

(define finite-positive-binary-p
  ((x real/rationalp "Floating point value")
   (f formatp "Floating point format"))
  :returns (yes booleanp :rule-classes ())
  (and (< 0 x)
       (or (nrepp x f)
           (drepp x f)))
  ///
  (defrule finite-positive-binary-fwd
    (implies (finite-positive-binary-p x f)
             (and (pos-rationalp x)
                  (formatp f)))
    :rule-classes :forward-chaining
    :enable (nrepp drepp))
  (acl2::with-arith5-help
   (defrule finite-positive-binary-necc
     (implies (finite-positive-binary-p x f)
              (let ((q (q x f))
                    (c (c x f)))
                (and (= x (* c (expt 2 q)))
                     (integerp q)
                     (<= (Qmin f) q)
                     (<= q (Qmax f))
                     (integerp c)
                     (or (and (<= (2^{P-1} f) c)
                              (<= c (Cmax f)))
                         (and (< 0 c)
                              (< c (2^{P-1} f))
                              (= q (Qmin f)))))))
     :rule-classes ()
     :hints (("subgoal 8" :in-theory (enable nrepp c))
             ("subgoal 3" :in-theory (enable drepp c))
             ("subgoal 2" :in-theory (enable Qmax-as-Qmin)))))
  (acl2::with-arith5-nonlinear-help
   (defrule finite-positive-binary-suff
     (implies (and (formatp f)
                   (integerp q)
                   (<= (Qmin f) q)
                   (<= q (Qmax f))
                   (integerp c)
                   (or (and (<= (2^{P-1} f) c)
                            (< c (* 2 (2^{P-1} f))))
                       (and (< 0 c)
                            (< c (2^{P-1} f))
                            (= q (Qmin f)))))
              (finite-positive-binary-p (* c (expt 2 q)) f))
     :cases ((<= (2^{P-1} f) c))
     :hints
     (("subgoal 2"
       :in-theory (enable Qmin 2^{P-1} P 2^{W-1}-as-bias
                          spd)
       :use (:instance spd-mult
                       (r (* c (expt 2 q)))
                       (m c)))
      ("subgoal 1" :in-theory (enable 2^{W-1}-as-bias
                                      Qmin Qmax 2^{P-1} P
                                      nrepp exactp sig expq bias expo-as-expe)
       :expand (expt 2 (expw f))
       :use ((:instance fp-rep-qc-unique
                       (b 2)
                       (p (P f))
                       (x (* c (expt 2 q))))
           (:instance expe-shift
                      (x c)
                      (n q)
                      (b 2))
           (:instance expe<=
                      (b 2)
                      (x c)
                      (n (1- (P f))))))))))

(defrule q-linear-when-finite-positive-binary
  (implies (finite-positive-binary-p x f)
           (<= (q x f) (Qmax f)))
  :rule-classes :linear
  :use finite-positive-binary-necc)

(defrule c-type-when-finite-positive-binary
  (implies (finite-positive-binary-p x f)
           (posp (c x f)))
  :rule-classes :type-prescription
  :use finite-positive-binary-necc)

(defrule c-linear-when-finite-positive-binary
  (implies (finite-positive-binary-p x f)
           (<= (c x f) (Cmax f)))
  :rule-classes :linear
  :enable Cmax
  :use finite-positive-binary-necc)

(rule
 (not (finite-positive-binary-p #f1.2 (dp)))
 :enable (dp))
