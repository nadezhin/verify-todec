;; ACL2 model of prototype implementation
;;
(in-package "RTL")
(include-book "section6")
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
     :enable (dp expf bvecp bits fl))))

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
     :enable (dp manf bvecp bits fl))))

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

(define out@
  ((enc acl2::ubyte64p))
  :returns (odd@ bitp :rule-classes :type-prescription)
  (acl2::logbit 0 (c@ enc))
  ///
  (fty::deffixequiv out@))

(define qb@
  ((enc acl2::ubyte64p))
  :returns (qb@ integerp :rule-classes :type-prescription)
  (if (or (= (q@ enc) (Qmin (dp)))
          (not (= (c@ enc) (2^{P-1} (dp)))))
      (- (q@ enc) 1)
    (- (q@ enc) 2))
  ///
  (fty::deffixequiv qb@))

(define cb@
  ((enc acl2::ubyte64p))
  :returns (cb@ natp :rule-classes :type-prescription)
  (if (or (= (q@ enc) (Qmin (dp)))
          (not (= (c@ enc) (2^{P-1} (dp)))))
      (* 2 (c@ enc))
    (* 4 (c@ enc)))
  ///
  (fty::deffixequiv cb@))

(define cbl@
  ((enc acl2::ubyte64p))
  :returns (cbl@ integerp :rule-classes :type-prescription)
  (- (cb@ enc) 1)
  ///
  (fty::deffixequiv cbl@))

(define cbr@
  ((enc acl2::ubyte64p))
  :returns (cb@ natp :rule-classes :type-prescription)
  (if (or (= (q@ enc) (Qmin (dp)))
          (not (= (c@ enc) (2^{P-1} (dp)))))
      (+ (cb@ enc) 1)
    (+ (cb@ enc) 2))
  ///
  (fty::deffixequiv cbr@))

(acl2::with-arith5-help
 (define r@
   ((enc acl2::ubyte64p))
   :returns (r@ integerp :rule-classes :type-prescription)
   (- (ordD (expt 2 (+ (qb@ enc) 1))) 1)
   ///
   (fty::deffixequiv r@)))

(acl2::with-arith5-help
 (define p5@
   ((enc acl2::ubyte64p))
   :returns (p5@ pos-rationalp :rule-classes :type-prescription)
   (expt 5 (- (r@ enc)))
   ///
   (fty::deffixequiv p5@)))

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
  (fty::deffixequiv p5.c@))

(define qq@
  ((enc acl2::ubyte64p))
  :returns (qq@ integerp :rule-classes :type-prescription)
  (+ (qb@ enc) (p5.q@ enc) (- (r@ enc)))
  ///
  (fty::deffixequiv qq@))

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
       (Prototype.toBigDecimal (sgn@ enc) (s10@ enc) (+ (r@ enc) 1)))
      ((not (uin10@ enc))
       (Prototype.toBigDecimal (sgn@ enc) (t10@ enc) (+ (r@ enc) 1)))
      ((not (and (uin10@ enc) (win10@ enc))) nil) ; AssertionError
      ((not (= (qb@ enc) (- (q@ enc) 2))) nil) ; AssertionError
      ((= (mod (s10@ enc) 10) 0)
       (Prototype.toBigDecimal (sgn@ enc) (s10@ enc) (+ (r@ enc) 1)))
      ((= (mod (t10@ enc) 10) 0)
       (Prototype.toBigDecimal (sgn@ enc) (t10@ enc) (+ (r@ enc) 1)))
      ((< (cmp10@ enc) 0)
       (Prototype.toBigDecimal (sgn@ enc) (s10@ enc) (+ (r@ enc) 1)))
      (t (Prototype.toBigDecimal (sgn@ enc) (t10@ enc) (+ (r@ enc) 1)))))
    ((when (= (s10@ enc) 0))
     (Prototype.toBigDecimal (sgn@ enc)
                             (if (= (s@ enc) 4) 49 99)
                             (- (r@ enc) 1)))
    ((unless (or (uin@ enc) (win@ enc))) nil) ; AssertionError
    ((when (not (win@ enc)))
     (Prototype.toBigDecimal (sgn@ enc) (s@ enc) (r@ enc)))
    ((when (not (uin@ enc)))
     (Prototype.toBigDecimal (sgn@ enc) (t@ enc) (r@ enc)))
    ((when (< (cmp@ enc) 0))
     (Prototype.toBigDecimal (sgn@ enc) (s@ enc) (r@ enc)))
    ((when (> (cmp@ enc) 0))
     (Prototype.toBigDecimal (sgn@ enc) (t@ enc) (r@ enc)))
    ((when (= (acl2::logbit 0 (s@ enc)) 0))
     (Prototype.toBigDecimal (sgn@ enc) (s@ enc) (r@ enc))))
   (Prototype.toBigDecimal (sgn@ enc) (t@ enc) (r@ enc)))
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

