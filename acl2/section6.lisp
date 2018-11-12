(in-package "RTL")
(include-book "section5")

(local (include-book "rtl/rel11/support/basic" :dir :system))
(local (include-book "rtl/rel11/support/float" :dir :system))
(local (acl2::allow-arith5-help))

(defrulel integerp-d*D^i
  (implies (and (integerp d)
                (natp i))
           (integerp (* d (expt (D) i))))
  :rule-classes ())

; Definition 3

(define D_i-p
  (x
   (i integerp))
  :returns (belongs booleanp :rule-classes ())
  (acl2::b*
   ((i (ifix i)))
   (and (real/rationalp x)
        (integerp (* x (expt (D) (- i))))))
  ///
  (fty::deffixequiv D_i-p)
  (defrule D_i-p-fwd
    (implies (D_i-p x i)
             (rationalp x))
    :rule-classes :forward-chaining))

(acl2::with-arith5-nonlinear++-help
 (defruled D_{i+1}
   (implies (D_i-p x (+ (ifix i) 1))
            (D_i-p x i))
   :enable (D_i-p (D))))

(define s_i
  ((v pos-rationalp)
   (i integerp))
  :returns (s_i natp :rule-classes :type-prescription)
  (acl2::b*
   ((v (pos-rational-fix v))
    (i (ifix i)))
   (fl (* v (expt (D) (- i)))))
  ///
  (fty::deffixequiv s_i)
  (defruled s_i-linear
    (<= (s_i v i)
        (* (pos-rational-fix v) (expt (D) (- (ifix i)))))
    :rule-classes ((:linear :trigger-terms ((s_i v i))))))

(define t_i
  ((v pos-rationalp)
   (i integerp))
  :returns (t_i posp :rule-classes ())
  (+ (s_i v i) 1)
  ///
  (fty::deffixequiv t_i)
  (defruled t_i-linear
    (> (t_i v i)
        (* (pos-rational-fix v) (expt (D) (- (ifix i)))))
    :rule-classes ((:linear :trigger-terms ((t_i v i))))
    :enable s_i))

(define u_i
  ((v pos-rationalp)
   (i integerp))
  :returns (u_i (and (rationalp u_i) (<= 0 u_i)) :rule-classes ())
  (* (s_i v i) (expt (D) (ifix i)))
  ///
  (fty::deffixequiv u_i)
  (acl2::with-arith5-nonlinear-help
   (defruled u_i-linear
     (<= (u_i v i) (pos-rational-fix v))
     :rule-classes :linear
     :use s_i-linear)))

(define w_i
  ((v pos-rationalp)
   (i integerp))
  :returns (w_i pos-rationalp :rule-classes ())
  (* (t_i v i) (expt (D) (ifix i)))
  ///
  (fty::deffixequiv w_i)
  (acl2::with-arith5-nonlinear-help
   (defruled w_i-linear
     (< (pos-rational-fix v) (w_i v i))
     :rule-classes :linear
     :use t_i-linear)))

(acl2::with-arith5-nonlinear++-help
 (defruled result-2-u
  (implies (and (D_i-p x i)
                (<= x (pos-rational-fix v))
                (not (= x (u_i v i))))
           (< x (u_i v i)))
  :enable (D_i-p u_i t_i)
  :use t_i-linear
  :cases ((<= (* x (expt (D) (- (ifix i)))) (s_i v i))
          (>= (* x (expt (D) (- (ifix i)))) (t_i v i)))))

(acl2::with-arith5-nonlinear++-help
 (defruled result-2-w
  (implies (and (D_i-p x i)
                (< (pos-rational-fix v) x)
                (not (= x (w_i v i))))
           (< (w_i v i) x))
  :enable (D_i-p w_i)
  :use s_i-linear
  :cases ((<= (* x (expt (D) (- (ifix i)))) (s_i v i))
          (>= (* x (expt (D) (- (ifix i)))) (t_i v i)))
  :prep-lemmas
  ((defrule lemma
     (equal (s_i v i)
            (1- (t_i v i)))
     :enable t_i))))

; Definition 5

(acl2::with-arith5-help
 (define largest-i
   ((d integerp)
    (i integerp))
   :measure (abs (ifix d))
   :returns (largest-i integerp :rule-classes ())
   (acl2::b*
    ((d (ifix d))
     (i (ifix i))
     ((when (= d 0)) 0)
     ((unless (integerp (/ d (D)))) i))
    (largest-i (/ d (D)) (+ i 1)))
   ///
   (fty::deffixequiv largest-i)
   (defrule largest-i-d=0
     (equal (largest-i 0 i) 0))
   (defrule largest-i>=i
     (implies (not (= (ifix d) 0))
              (>= (largest-i d i) (ifix i)))
     :rule-classes :linear)
   (defrule D^{largest-i-minis-i}-divides-d
      (acl2::b*
       ((li (largest-i d i))
        (d (ifix d))
        (i (ifix i)))
       (integerp (* d (expt (D) (- i li)))))
      :rule-classes ())
   (acl2::with-arith5-nonlinear-help
    (defrule D^{largest-i+1-minis-i}-not-divides-d
      (acl2::b*
       ((li (largest-i d i))
        (d (ifix d))
        (i (ifix i)))
       (implies (not (= d 0))
                (not (integerp (* d (expt (D) (1- (- i li))))))))
      :induct (largest-i d i)
      :rule-classes ()))
   (defrule largest-i-unique
     (implies (= (D-value d1 i1) (D-value d2 i2))
              (= (largest-i d1 i1) (largest-i d2 i2)))
     :rule-classes ()
     :use (:instance lemma2
                     (d1 (ifix d1))
                     (i1 (ifix i1))
                     (d2 (ifix d2))
                     (i2 (ifix i2)))
     :prep-lemmas
     ((defrule lemma1
        (implies (and (integerp d)
                      (integerp i)
                      (integerp i-new)
                      (<= i i-new)
                      (integerp (* d (expt (D) (- i i-new)))))
                 (equal (largest-i d i)
                        (largest-i (* d (expt (D) (- i i-new))) i-new)))
        :rule-classes ()
        :induct (largest-i d i)
        :hints (("subgoal *1/3" :use (:instance integerp-d*D^i
                                                (d (* d (expt (D) (- i i-new))))
                                                (i (- (1- i-new) i))))))
      (defrule lemma2
        (implies (and (integerp d1)
                      (integerp i1)
                      (integerp d2)
                      (integerp i2)
                      (= (D-value d1 i1) (D-value d2 i2)))
                 (equal (largest-i d1 i1) (largest-i d2 i2)))
        :rule-classes ()
        :enable D-value
        :cases ((< i1 i2) (> i1 i2))
        :hints (("subgoal 2" :use (:instance lemma1
                                             (d d1)
                                             (i i1)
                                             (i-new i2)))
                ("subgoal 1" :use (:instance lemma1
                                             (d d2)
                                             (i i2)
                                             (i-new i1)))))))
   (defruled D_i-p-as-largest-i
     (equal (D_i-p (D-value d i) i?)
            (or (= (ifix d) 0)
                (<= (ifix i?) (largest-i d i))))
     :use (:instance lemma
                     (d (ifix d))
                     (i (ifix i))
                     (i? (ifix i?)))
     :prep-lemmas
     ((defruled lemma
        (implies (and (integerp d)
                      (integerp i)
                      (integerp i?))
                 (equal (D_i-p (D-value d i) i?)
                        (or (= d 0)
                            (<= (ifix i?) (largest-i d i)))))
        :enable (D_i-p D-value)
        :hints
        (("subgoal 2" :use
          (D^{largest-i-minis-i}-divides-d
           (:instance integerp-d*D^i
                      (d (* d (expt (D) (- i (largest-i d i)))))
                      (i (- (largest-i d i) i?)))))
         ("subgoal 1" :use
          (D^{largest-i+1-minis-i}-not-divides-d
           (:instance integerp-d*D^i
                      (d (* d (expt (D) (- i i?))))
                      (i (- i? (1+ (largest-i d i)))))))))))))

(define shortest-d
  ((d integerp)
   (i integerp))
  :returns (shortest-d integerp :rule-classes :type-prescription
                       :hints (("goal" :in-theory (disable ifix)
                                :use D^{largest-i-minis-i}-divides-d)))
  (acl2::b*
   ((d (ifix d))
    (i (ifix i)))
   (* d (expt (D) (- i (largest-i d i)))))
  ///
  (fty::deffixequiv shortest-d)
  (defrule shortest-d-d=0
    (equal (shortest-d 0 i) 0))
  (acl2::with-arith5-help
   (defrule D-not-fivides-shortest-d
     (implies (not (= (ifix d) 0))
              (not (integerp (* (/ (D)) (shortest-d d i)))))
     :use D^{largest-i+1-minis-i}-not-divides-d
     :disable ifix))
  (acl2::with-arith5-help
   (defrule D-value-shortest-d-largest-i
     (equal (D-value (shortest-d d i) (largest-i d i))
            (D-value d i))
     :enable D-value
     :use D^{largest-i-minis-i}-divides-d
     :cases ((integerp i))
     :hints (("subgoal 2" :expand ((largest-i d i) (largest-i d 0))))))
   (defrule shortest-d-unique
     (implies (= (D-value d1 i1) (D-value d2 i2))
              (= (shortest-d d1 i1) (shortest-d d2 i2)))
     :rule-classes ()
     :use (:instance lemma
                     (d1 (ifix d1))
                     (i1 (ifix i1))
                     (d2 (ifix d2))
                     (i2 (ifix i2)))
     :prep-lemmas
     ((acl2::with-arith5-help
       (defruled lemma
        (implies (and (= (D-value d1 i1) (D-value d2 i2))
                      (integerp d1)
                      (integerp i1)
                      (integerp d2)
                      (integerp i2))
                 (= (shortest-d d1 i1) (shortest-d d2 i2)))
        :enable D-value
        :use largest-i-unique))))
  (acl2::with-arith5-nonlinear-help
   (defrule D-length-shortest-d<=D-length-d
     (<= (D-length (shortest-d d i)) (D-length d))
     :enable D-length
     :use (largest-i>=i
           D^{largest-i-minis-i}-divides-d
           (:instance expe-shift
                      (b (D))
                      (x (ifix d))
                      (n (- (ifix i) (largest-i d i)))))
     :cases ((integerp i))
     :hints (("subgoal 2" :expand ((largest-i d i) (largest-i d 0)))))))

; Definition 5

(define D-len
   ((d integerp)
    (i integerp))
   :returns (D-len posp :rule-classes :type-prescription)
   (D-length (shortest-d d i))
   ///
   (fty::deffixequiv D-len)
   (defrule D-len-unique
     (implies (= (D-value d1 i1) (D-value d2 i2))
              (equal (D-len d1 i1) (D-len d2 i2)))
     :rule-classes ()
     :use shortest-d-unique)
   (defrule D-len<=D-length
     (<= (D-len d i) (D-length d))
     :rule-classes :linear)
   (defruled D-len-as-expe-D-value
     (equal (D-len d i)
            (- (+ (expe (D-value d i) (D)) 1) (largest-i d i)))
     :use (:instance lemma
                     (d (ifix d))
                     (i (ifix i)))
     :prep-lemmas
     ((defrule expe-shift-alt
        (implies (and (real/rationalp x)
                      (not (= x 0))
                      (integerp n))
                 (equal (expe (* x (expt (D) n)) (D))
                        (+ n (expe x (D)))))
        :use (:instance expe-shift (b (D))))
      (acl2::with-arith5-help
       (defrule lemma
        (implies (and (integerp d)
                      (integerp i))
                 (equal (D-len d i)
                        (- (+ (expe (D-value d i) (D)) 1) (largest-i d i))))
        :enable (D-length D-value shortest-d expe-shift)
        :use D^{largest-i-minis-i}-divides-d
        :cases ((= d 0)))))))

(defruledl result-3-largest-i{d?}<i
  (acl2::b*
   ((x (D-value d i))
    (x? (D-value d? i?))
    (D^i (expt (D) i)))
   (implies (and (< (- x D^i) x?)
                 (< x? (+ x D^i))
                 (not (= x? x)))
            (< (largest-i d? i?) (ifix i))))
  :rule-classes :linear
  :disable ifix
  :use (:instance lemma
                  (d (ifix d))
                  (i (ifix i))
                  (d? (ifix d?))
                  (i? (ifix i?)))
  :prep-lemmas
  ((acl2::with-arith5-nonlinear++-help
    (defrule lemma
      (acl2::b*
       ((x (D-value d i))
        (x? (D-value d? i?))
        (D^i (expt (D) i)))
       (implies (and (integerp d)
                     (integerp i)
                     (integerp d?)
                     (integerp i?)
                     (< (- x D^i) x?)
                     (< x? (+ x D^i))
                     (not (= x? x)))
                (<= (largest-i d? i?) (- i 1))))
      :cases ((not (integerp (* (D-value d? i?) (expt (D) (- i)))))
              (<= d (1- (* (D-value d? i?) (expt (D) (- i)))))
              (=  d     (* (D-value d? i?) (expt (D) (- i))))
              (>= d (1+ (* (D-value d? i?) (expt (D) (- i))))))
      :enable D-value
      :use
      ((:instance D^{largest-i-minis-i}-divides-d
                  (d d?)
                  (i i?))
       (:instance integerp-d*D^i
                  (d (* (D-value d? i?) (expt (D) (- (largest-i d? i?)))))
                  (i (- (largest-i d? i?) i))))))))

(local
 (acl2::with-arith5-nonlinear-help
  (defruled result-3-expe-x?-linear
    (acl2::b*
     ((x (D-value d i))
      (D^i (expt (D) i)))
     (implies (and (integerp d)
                   (<= 2 (abs d))
                   (integerp i)
                   (real/rationalp x?)
                   (< (- x D^i) x?)
                   (< x? (+ x D^i)))
              (>= (expe x? (D)) (- (expe x (D)) 1))))
    :enable D-value
    :use ((:instance expe-monotone
                     (b (D))
                     (x (/ (D-value d i) (D)))
                     (y x?))
          (:instance expe-shift
                     (b (D))
                     (x (D-value d i))
                     (n -1))))))

(acl2::with-arith5-help
 (defrule result-3
  (acl2::b*
   ((x (D-value d i))
    (x? (D-value d? i?))
    (D^i (expt (D) (ifix i))))
   (implies (and (< (- x D^i) x?)
                 (< x? (+ x D^i)))
   (>= (D-len d? i?) (D-len d i))))
  :cases ((< (abs (ifix d)) 2)
          (= (D-value d i) (D-value d? i?)))
  :hints
  (("subgoal 3" :in-theory (enable D-len-as-expe-D-value)
    :use (result-3-largest-i{d?}<i
          (:instance result-3-expe-x?-linear
                     (i (ifix i))
                     (x? (D-value d? i?)))))
   ("subgoal 2" :cases ((= (D-len d i) 1)))
   ("subgoal 2.2" :cases ((= d -1) (= d 1))
    :in-theory (enable D-len shortest-d largest-i))
   ("subgoal 1" :use (:instance D-len-unique
                                (d1 d)
                                (i1 i)
                                (d2 d?)
                                (i2 i?))))))
