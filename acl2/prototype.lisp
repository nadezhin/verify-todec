;; ACL2 model of prototype implementation
;;
(in-package "RTL")
(include-book "section11")
(include-book "ihs/basic-definitions" :dir :system)
(include-book "kestrel/utilities/fixbytes/instances" :dir :system)

(local (acl2::allow-arith5-help))

(local (include-book "rtl/rel11/support/basic" :dir :system))
(local (include-book "rtl/rel11/support/bits" :dir :system))
(local (include-book "rtl/rel11/support/float" :dir :system))
(local (include-book "rtl/rel11/support/reps" :dir :system))

(define Prototype.toBigDecimal
  ((sgn booleanp)
   (d natp)
   (r integerp))
  :returns (decimal rationalp)
  (* (if sgn -1 1)
     (nfix d)
     (expt (D) r))
  ///
  (fty::deffixequiv Prototype.toBigDecimal))

(define enc@
  ((enc acl2::ubyte64p))
  :returns (enc@ (encodingp enc@ (dp))
                 :hints (("goal" :in-theory (enable encodingp
                                                    dp
                                                    acl2::ubyte64-fix
                                                    acl2::ubyte64p
                                                    bvecp))))
  (acl2::ubyte64-fix enc)
  ///
  (fty::deffixequiv enc@))

(define sgnf@
  ((enc acl2::ubyte64p))
  :returns (sgnf@ bitp :rule-classes :type-prescription
                  :hints (("goal" :in-theory (enable sgnf))))
  (sgnf (enc@ enc) (dp))
  ///
  (fty::deffixequiv sgnf@))

(define sgn@
  ((enc acl2::ubyte64p))
  :returns (sgn@ booleanp :rule-classes :type-prescription)
  (= (sgnf@ enc) 1)
  ///
  (fty::deffixequiv sgn@))

(define expf@
  ((enc acl2::ubyte64p))
  :returns (expf@ natp :rule-classes :type-prescription)
  (expf (enc@ enc) (dp))
  ///
  (fty::deffixequiv expf@)
  (acl2::with-arith5-help
   (defrule expf@-linear
     (< (expf@ enc) (* 2 (2^{W-1} (dp))))
     :rule-classes ((:linear :trigger-terms ((expf@ enc))))
     :enable (dp expf bvecp bits fl)))
  (defruled expf@-when-denormp
    (implies (denormp (enc@ enc) (dp))
             (equal (expf@ enc) 0))
    :enable denormp)
  (defruled expf@-when-normp
    (implies (normp (enc@ enc) (dp))
             (and (<= 1 (expf@ enc))
                  (<= (expf@ enc) (1- (* 2 (2^{W-1} (dp)))))))
    :rule-classes ((:linear :trigger-terms ((expf@ enc))))
    :enable (normp dp)))

(define manf@
  ((enc acl2::ubyte64p))
  :returns (manf@ natp :rule-classes :type-prescription)
  (manf (enc@ enc) (dp))
  ///
  (fty::deffixequiv manf@)
  (acl2::with-arith5-help
   (defrule manf@-linear
     (< (manf@ enc) (2^{P-1} (dp)))
     :rule-classes ((:linear :trigger-terms ((manf@ enc))))
     :enable (dp manf bvecp bits fl)))
  (defrule manf@-when-denormp
    (implies (denormp (enc@ enc) (dp))
             (posp (manf@ enc)))
    :rule-classes :type-prescription
    :enable (denormp dp sigf manf)))

(defruledl decode-when-denormp
  (implies (denormp (enc@ enc) (dp))
           (equal (decode (enc@ enc) (dp))
                  (* (if (= (sgnf@ enc) 1) -1 1)
                     (manf@ enc)
                     (expt 2 (Qmin (dp))))))
  :enable (sgnf@ manf@ decode ddecode denormp sigf manf dp)
  :cases ((= (sgnf@ enc) 0)
          (= (sgnf@ enc) 1)))

(local
 (acl2::with-arith5-help
  (defruled decode-when-normp
    (implies (normp (enc@ enc) (dp))
             (equal (decode (enc@ enc) (dp))
                    (* (if (= (sgnf@ enc) 1) -1 1)
                       (+ (2^{P-1} (dp)) (manf@ enc))
                       (expt 2 (+ -1 (Qmin (dp)) (expf@ enc))))))
    :enable (sgnf@ expf@ manf@ decode ndecode normp dp)
    :cases ((= (sgnf@ enc) 0)
            (= (sgnf@ enc) 1)))))

(acl2::with-arith5-help
 (define abs-val@
   ((enc acl2::ubyte64p))
   :returns (abs-val@ pos-rationalp
                      :rule-classes :type-prescription
                      :hints (("goal" :in-theory (enable decode-when-denormp
                                                         decode-when-normp))))
   (acl2::b*
    ((enc (enc@ enc))
     (f (dp)))
    (if (or (denormp enc f) (normp enc f))
        (abs (decode enc f))
      1))
   ///
   (fty::deffixequiv abs-val@)
   (defruled abs-val@-when-denormp
     (implies (denormp (enc@ enc) (dp))
              (equal (abs-val@ enc)
                     (* (manf@ enc)
                        (expt 2 (Qmin (dp))))))
     :enable decode-when-denormp)
   (defruled abs-val@-when-normp
     (implies (normp (enc@ enc) (dp))
              (equal (abs-val@ enc)
                     (* (+ (2^{P-1} (dp)) (manf@ enc))
                        (expt 2 (+ -1 (Qmin (dp)) (expf@ enc))))))
     :enable decode-when-normp)))

(define q@
  ((enc acl2::ubyte64p))
  :returns (q@ integerp :rule-classes :type-prescription)
  (if (= (expf@ enc) 0)
      (Qmin (dp))
    (+ (1- (expf@ enc)) (Qmin (dp))))
  ///
  (fty::deffixequiv q@)
  (defrule q@-denormp
    (implies (denormp (enc@ enc) (dp))
             (equal (q@ enc) (Qmin (dp))))
    :enable (denormp expf@))
  (defrule q@-normp-linear
    (implies (normp (enc@ enc) (dp))
             (and (<= (Qmin (dp)) (q@ enc))
                  (<= (q@ enc) (Qmax (dp)))))
    :rule-classes ((:linear :trigger-terms ((q@ enc))))
    :enable (normp expf@ dp)))

(define c@
  ((enc acl2::ubyte64p))
  :returns (c@ natp :rule-classes :type-prescription)
  (if (= (expf@ enc) 0)
      (manf@ enc)
    (+ (manf@ enc) (2^{P-1} (dp))))
  ///
  (fty::deffixequiv c@))

(acl2::with-arith5-help
 (defruled abs-val@-as-c@*2^q@
  (implies (or (denormp (enc@ enc) (dp)) (normp (enc@ enc) (dp)))
           (equal (abs-val@ enc)
                  (* (c@ enc)
                     (expt 2 (q@ enc)))))
  :enable (abs-val@-when-denormp
           abs-val@-when-normp
           q@ c@)))

(defruled c@-q@-as-abs-val@
  (implies (or (denormp (enc@ enc) (dp))
               (normp (enc@ enc) (dp)))
           (and (equal (q@ enc) (q (abs-val@ enc) (dp)))
                (equal (c@ enc) (c (abs-val@ enc) (dp)))))
  :enable c@
  :use (abs-val@-as-c@*2^q@
        (:instance unique-c*2^q
                   (f (dp))
                   (q (q@ enc))
                   (c (c@ enc)))))

(defrule finite-positive-double-abs-val@
  (implies (or (denormp (enc@ enc) (dp))
               (normp (enc@ enc) (dp)))
           (finite-positive-binary-p (abs-val@ enc) (dp)))
  :cases ((= (decode (enc@ enc) (dp)) 0))
  :enable (finite-positive-binary-p abs-val@ decode)
  :hints (("subgoal 2" :use (:instance lemma1
                                       (f (dp))
                                       (x (ddecode (enc@ enc) (dp)))))
          ("subgoal 1" :use (:instance decode-0
                                       (f (dp))
                                       (x (enc@ enc)))))
  :prep-lemmas
  ((defrule lemma1
     (implies (drepp x f)
              (drepp (- x) f))
     :enable drepp)
   (defrule lemma2
     (implies (nrepp x f)
              (nrepp (- x) f))
     :enable nrepp)
   (defrule lemma3
     (implies (denormp x f)
              (equal (expf x f) 0))
     :enable denormp)
   (Defrule lemma4
     (implies (normp x f)
              (not (equal (expf x f) 0)))
     :enable normp)))

(define out@
  ((enc acl2::ubyte64p))
  :returns (odd@ bitp :rule-classes :type-prescription)
  (acl2::logbit 0 (c@ enc))
  ///
  (fty::deffixequiv out@)
  (defruled out@-as-abs-val@
    (implies (or (denormp (enc@ enc) (dp))
                 (normp (enc@ enc) (dp)))
             (equal (out@ enc)
                    (acl2::bool->bit
                      (not (integerp (* 1/2 (c (abs-val@ enc) (dp))))))))
    :cases ((integerp (c@ enc)))
    :enable (c@-q@-as-abs-val@)
    :disable logbitp
    :prep-lemmas
    ((acl2::with-arith5-help
      (defrule lemma
        (implies (integerp x)
                 (equal (integerp (* 1/2 x))
                        (not (logbitp 0 x)))))))))

(define qb@
  ((enc acl2::ubyte64p))
  :returns (qb@ integerp :rule-classes :type-prescription)
  (if (or (= (q@ enc) (Qmin (dp)))
          (not (= (c@ enc) (2^{P-1} (dp)))))
      (- (q@ enc) 1)
    (- (q@ enc) 2))
  ///
  (fty::deffixequiv qb@)
  (defruled qb@-as-abs-val@
    (implies (or (denormp (enc@ enc) (dp))
                 (normp (enc@ enc) (dp)))
             (equal (qb@ enc) (qb (abs-val@ enc) (dp))))
    :enable (c@-q@-as-abs-val@ qb)))

(define cb@
  ((enc acl2::ubyte64p))
  :returns (cb@ natp :rule-classes :type-prescription)
  (if (or (= (q@ enc) (Qmin (dp)))
          (not (= (c@ enc) (2^{P-1} (dp)))))
      (* 2 (c@ enc))
    (* 4 (c@ enc)))
  ///
  (fty::deffixequiv cb@)
  (defruled cb@-as-abs-val@
    (implies (or (denormp (enc@ enc) (dp))
                 (normp (enc@ enc) (dp)))
             (equal (cb@ enc) (cb (abs-val@ enc) (dp))))
    :enable (c@-q@-as-abs-val@ cb)))

(define cbl@
  ((enc acl2::ubyte64p))
  :returns (cbl@ integerp :rule-classes :type-prescription)
  (- (cb@ enc) 1)
  ///
  (fty::deffixequiv cbl@)
  (defruled cbl@-as-abs-val@
    (implies (or (denormp (enc@ enc) (dp))
                 (normp (enc@ enc) (dp)))
             (equal (cbl@ enc) (cbl (abs-val@ enc) (dp))))
    :enable (cb@-as-abs-val@ cbl)))

(define cbr@
  ((enc acl2::ubyte64p))
  :returns (cb@ natp :rule-classes :type-prescription)
  (if (or (= (q@ enc) (Qmin (dp)))
          (not (= (c@ enc) (2^{P-1} (dp)))))
      (+ (cb@ enc) 1)
    (+ (cb@ enc) 2))
  ///
  (fty::deffixequiv cbr@)
  (defruled cbr@-as-abs-val@
    (implies (or (denormp (enc@ enc) (dp))
                 (normp (enc@ enc) (dp)))
             (equal (cbr@ enc) (cbr (abs-val@ enc) (dp))))
    :enable (c@-q@-as-abs-val@ cb@-as-abs-val@ cbr)))

(acl2::with-arith5-help
 (define k@
   ((enc acl2::ubyte64p))
   :returns (k@ integerp :rule-classes :type-prescription)
   (- (ordD (expt 2 (+ (qb@ enc) 1))) 1)
   ///
   (fty::deffixequiv k@)
   (defruled k@-def
    (and (<= (* 1/2 (expt (D) (k@ enc))) (expt 2 (qb@ enc)))
         (< (expt 2 (qb@ enc)) (* 1/2 (expt (D) (1+ (k@ enc))))))
    :rule-classes ((:linear :trigger-terms ((expt 2 (qb@ enc)))))
    :use (:instance result-1-3
                    (x (expt 2 (1+ (qb@ enc))))
                    (k (1+ (k@ enc)))))
   (acl2::with-arith5-nonlinear-help
   (defrule k@-linear
    (implies (or (denormp (enc@ enc) (dp))
                 (normp (enc@ enc) (dp)))
             (and (<= -324 (k@ enc))
                  (<= (k@ enc) 292)))
    :rule-classes :linear
    :cases ((and (<= (Qmin (dp)) (1+ (qb@ enc)))
                 (<= (1+ (qb@ enc)) (Qmax (dp)))))
    :hints
    (("subgoal 2" :in-theory (enable qb@-as-abs-val@))
     ("subgoal 1" :in-theory (enable dp) :use
      ((:instance result-1-4
                  (x (expt 2 (Qmin (dp))))
                  (y (expt 2 (1+ (qb@ enc)))))
       (:instance result-1-4
                  (x (expt 2 (1+ (qb@ enc))))
                  (y (expt 2 (Qmax (dp))))))))))))

(acl2::with-arith5-help
 (define alpha@
   ((enc acl2::ubyte64p))
   :returns (alpha@ pos-rationalp :rule-classes :type-prescription)
   (/ (expt 2 (qb@ enc)) (* 1/2 (expt (D) (k@ enc))))
   ///
   (fty::deffixequiv alpha@)
   (acl2::with-arith5-nonlinear-help
    (defrule alpha@-linear
      (and (<= 1 (alpha@ enc))
           (< (alpha@ enc) (D)))
      :rule-classes :linear
      :enable k@-def)
   (defruled alpha@-as-expt-D/2
     (equal (alpha@ enc)
            (* (expt 2 (+ 1 (qb@ enc) (- (k@ enc))))
               (expt (D/2) (- (k@ enc)))))
     :enable expt-D-as-expt-D/2))))

(acl2::with-arith5-help
 (define p5@
   ((enc acl2::ubyte64p))
   :returns (p5@ pos-rationalp :rule-classes :type-prescription)
   (expt (D/2) (- (k@ enc)))
   ///
   (fty::deffixequiv p5@)
   (defruled alpha@-as-p5@
     (equal (alpha@ enc)
            (* (p5@ enc) (expt 2 (+ 1 (qb@ enc) (- (k@ enc))))))
     :enable alpha@-as-expt-D/2)))

(define p5.q@
  ((enc acl2::ubyte64p))
  :returns (p5.q@ integerp :rule-classes :type-prescription)
  (expq (p5@ enc) 126 2)
  ///
  (fty::deffixequiv p5.q@))

(define p5.c@
  ((enc acl2::ubyte64p))
  :returns (p5.c@ posp :rule-classes :type-prescription)
  (cg (sigc (p5@ enc) 126 2))
  ///
  (fty::deffixequiv p5.c@)
  (defrule p5.c@-bounds
    (and (<= #fx1p125 (p5.c@ enc))
         (<= (p5.c@ enc) #fx1p126))
    :rule-classes :linear
    :enable (sigc-lower-bound sigc-upper-bound))
  (acl2::with-arith5-help
   (defruled p5.c@-linear-old
     (let ((a (* (alpha@ enc)
                 (expt 2 (- (1- (k@ enc)) (+ (qb@ enc) (p5.q@ enc)))))))
       (and (<= a (p5.c@ enc))
            (< (p5.c@ enc) (1+ a))))
     :rule-classes ((:linear :trigger-terms ((p5.c@ enc))))
     :enable (alpha@-as-p5@ p5.q@ cg-def sigc sigm expq))))

(define qq@
  ((enc acl2::ubyte64p))
  :returns (qq@ integerp :rule-classes :type-prescription)
  (+ (qb@ enc) (p5.q@ enc) (- (k@ enc)))
  ///
  (fty::deffixequiv qq@)
  (acl2::with-arith5-help
   (defruled p5.c@-linear
     (let ((a (* 1/2 (alpha@ enc) (expt 2 (- (qq@ enc))))))
       (and (<= a (p5.c@ enc))
            (< (p5.c@ enc) (1+ a))))
     :rule-classes ((:linear :trigger-terms ((p5.c@ enc))))
     :enable (alpha@-as-p5@ p5.q@ p5.c@ cg-def sigc sigm expq))))

(define sh@
  ((enc acl2::ubyte64p))
  :returns (sh@ integerp :rule-classes :type-prescription)
  (- (- (qq@ enc)) 65)
  ///
  (fty::deffixequiv sh@))

(define Vl@
  ((enc acl2::ubyte64p))
  :returns (Vl@ integerp :rule-classes :type-prescription)
  (ash (* (p5.c@ enc) (cbl@ enc)) (- (sh@ enc)))
  ///
  (fty::deffixequiv Vl@))

(acl2::with-arith5-help
 (define V@
   ((enc acl2::ubyte64p))
   :returns (V@ natp :rule-classes :type-prescription)
   (ash (* (p5.c@ enc) (cb@ enc)) (- (sh@ enc)))
   ///
   (fty::deffixequiv V@)))

(acl2::with-arith5-help
 (define Vr@
   ((enc acl2::ubyte64p))
   :returns (Vr@ natp :rule-classes :type-prescription)
   (ash (* (p5.c@ enc) (cbr@ enc)) (- (sh@ enc)))
   ///
   (fty::deffixequiv Vr@)))

(define s@
  ((enc acl2::ubyte64p))
  :returns (s@ natp :rule-classes :type-prescription)
  (ash (V@ enc) -65)
  ///
  (fty::deffixequiv s@))

(define t@
  ((enc acl2::ubyte64p))
  :returns (t@ posp :rule-classes :type-prescription)
  (+ (s@ enc) 1)
  ///
  (fty::deffixequiv t@))

(define s10@
  ((enc acl2::ubyte64p))
  :returns (s10@ natp :rule-classes :type-prescription)
  (fl (/ (s@ enc) 10))
  ///
  (fty::deffixequiv s10@))

(define t10@
  ((enc acl2::ubyte64p))
  :returns (t10@ posp :rule-classes :type-prescription)
  (+ (s10@ enc) 1)
  ///
  (fty::deffixequiv t10@))

(define uin10@
  ((enc acl2::ubyte64p))
  :returns (uin10@ booleanp :rule-classes :type-prescription)
  (<= (+ (signum (- (Vl@ enc) (* (s10@ enc) (ash 10 65)))) (out@ enc))
      0)
  ///
  (fty::deffixequiv uin10@))

(define win10@
  ((enc acl2::ubyte64p))
  :returns (win10@ booleanp :rule-classes :type-prescription)
  (<= (+ (signum (- (* (t10@ enc) (ash 10 65)) (Vr@ enc))) (out@ enc))
      0)
  ///
  (fty::deffixequiv win10@))

(define cmp10@
  ((enc acl2::ubyte64p))
  :returns (win@ integerp :rule-classes :type-prescription)
  (signum (- (V@ enc) (* (+ (s10@ enc) (t10@ enc)) (ash 10 64))))
  ///
  (fty::deffixequiv cmp10@))

(define uin@
  ((enc acl2::ubyte64p))
  :returns (uin@ booleanp :rule-classes :type-prescription)
  (<= (+ (signum (- (Vl@ enc) (* (s@ enc) (ash 1 65)))) (out@ enc))
      0)
  ///
  (fty::deffixequiv uin@))

(define win@
  ((enc acl2::ubyte64p))
  :returns (win@ booleanp :rule-classes :type-prescription)
  (<= (+ (signum (- (* (t@ enc) (ash 1 65)) (Vr@ enc))) (out@ enc))
      0)
  ///
  (fty::deffixequiv win@))

(define cmp@
  ((enc acl2::ubyte64p))
  :returns (win@ integerp :rule-classes :type-prescription)
  (signum (- (V@ enc) (* (+ (s@ enc) (t@ enc)) (ash 1 64))))
  ///
  (fty::deffixequiv cmp@))

(local (in-theory (disable (tau-system))))

(define Prototype.toDecimal
  ((enc acl2::ubyte64p))
  :returns (decimal (or (null decimal)
                        (rationalp decimal))
                    :rule-classes :type-prescription)
  (acl2::b*
   ((f (dp))
    ((when (zerp (enc@ enc) f)) 0)
    ((when (and (>= (s10@ enc) 10)
                (or (uin10@ enc)
                    (win10@ enc))))
     (cond
      ((not (win10@ enc))
       (Prototype.toBigDecimal (sgn@ enc) (s10@ enc) (+ (k@ enc) 1)))
      ((not (uin10@ enc))
       (Prototype.toBigDecimal (sgn@ enc) (t10@ enc) (+ (k@ enc) 1)))
      ((not (and (uin10@ enc) (win10@ enc))) nil) ; AssertionError
      ((not (= (qb@ enc) (- (q@ enc) 2))) nil) ; AssertionError
      ((= (mod (s10@ enc) 10) 0)
       (Prototype.toBigDecimal (sgn@ enc) (s10@ enc) (+ (k@ enc) 1)))
      ((= (mod (t10@ enc) 10) 0)
       (Prototype.toBigDecimal (sgn@ enc) (t10@ enc) (+ (k@ enc) 1)))
      ((< (cmp10@ enc) 0)
       (Prototype.toBigDecimal (sgn@ enc) (s10@ enc) (+ (k@ enc) 1)))
      (t (Prototype.toBigDecimal (sgn@ enc) (t10@ enc) (+ (k@ enc) 1)))))
    ((when (= (s10@ enc) 0))
     (Prototype.toBigDecimal (sgn@ enc)
                             (if (= (s@ enc) 4) 49 99)
                             (- (k@ enc) 1)))
    ((unless (or (uin@ enc) (win@ enc))) nil) ; AssertionError
    ((when (not (win@ enc)))
     (Prototype.toBigDecimal (sgn@ enc) (s@ enc) (k@ enc)))
    ((when (not (uin@ enc)))
     (Prototype.toBigDecimal (sgn@ enc) (t@ enc) (k@ enc)))
    ((when (< (cmp@ enc) 0))
     (Prototype.toBigDecimal (sgn@ enc) (s@ enc) (k@ enc)))
    ((when (> (cmp@ enc) 0))
     (Prototype.toBigDecimal (sgn@ enc) (t@ enc) (k@ enc)))
    ((when (= (acl2::logbit 0 (s@ enc)) 0))
     (Prototype.toBigDecimal (sgn@ enc) (s@ enc) (k@ enc))))
   (Prototype.toBigDecimal (sgn@ enc) (t@ enc) (k@ enc)))
  ///
  (fty::deffixequiv Prototype.toDecimal
                    :hints (("goal" :in-theory (disable (tau-system))))))

(define check
  ((enc acl2::ubyte64p))
  :returns (yes booleanp)
  :guard-hints (("goal" :in-theory (enable encodingp
                                           acl2::ubyte64p
                                           bvecp dp)))
  (and (pos-rationalp (decode enc (dp)))
       (equal (Prototype.toDecimal enc)
              (algo1 2 (decode enc (dp)) (dp)))))

(rule
 (and
  (check 1)
  (check 2)
  (check 3)
  (check #x20)
  (check #x000fffffffffffff)
  (check #x0010000000000000)
  (check #x3ff0000000000000)
  (check #x7fefffffffffffff)))

