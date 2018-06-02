(in-package "RTL")
(include-book "section5")

(local (include-book "rtl/rel11/support/basic" :dir :system))
(local (include-book "rtl/rel11/support/float" :dir :system))
(local (include-book "rtl/rel11/support/reps" :dir :system))
(local (acl2::allow-arith5-help))

(acl2::with-arith5-help
 (defruled has-D-length-c*2^q
   (implies (and (posp c)
                 (integerp q))
            (let* ((x (* c (expt 2 q)))
                   (factor (if (<= 0 q) (expt 2 q) (expt (/ (D) 2) (- q))))
                   (i (ordD (* c factor))))
              (has-D-length x i)))
   :use ((:instance has-D-length-suff
                    (r (if (<= 0 q) 0 q))
                    (d (* c (expt 2 q) (expt (D) (if (<= 0 q) 0 (- q))))))
         (:instance lemma (half-D (/ (D) 2))))
   :prep-lemmas
   ((defruled lemma
      (implies (and (integerp q)
                    (< q 0)
                    (posp half-D))
               (integerp (* (expt 2 q) (expt (* 2 half-D) (- q)))))))))

(defrule has-D-length-when-finite-positive-binary
  (implies (finite-positive-binary-p v f)
           (let* ((q (q v f))
                  (c (c v f))
                  (factor (if (<= 0 q) (expt 2 q) (expt (/ (D) 2) (- q))))
                  (i (ordD (* c factor))))
             (has-D-length v i)))
  :use ((:instance finite-positive-binary-necc
                   (x v))
        (:instance has-D-length-c*2^q
                   (c (c v f))
                   (q (q v f)))))

(local
 (acl2::with-arith5-help
  (defrule s_i-lemma
    (implies (posp i)
             (and (<= (expt (D) (1- i)) (fl (* (f v) (expt (D) i))))
                  (< (fl (* (f v) (expt (D) i))) (expt (D) i))))
    :use (:instance result-1-1
                    (x (* (f v) (expt (D) i)))
                    (m (expt (D) (1- i)))
                    (n (expt (D) i))))))

(define s_i
  ((i posp)
   (v pos-rationalp))
  :returns (s_i posp :rule-classes :type-prescription
                :hints (("goal":use (:instance s_i-lemma
                                               (i (acl2::pos-fix i))))))
  (fl (* (f v) (expt (D) (acl2::pos-fix i))))
  ///
  (fty::deffixequiv s_i)
  (defruled s_i-linear
    (let* ((s_i (s_i i v))
           (i (acl2::pos-fix i)))
      (and (<= (expt (D) (- i 1)) s_i)
           (< (1- (* (f v) (expt (D) i))) s_i)
           (<= s_i (* (f v) (expt (D) i)))
           (< s_i (expt (D) i))))
    :rule-classes ((:linear :trigger-terms ((s_i i v))))
    :use (:instance s_i-lemma
                    (i (acl2::pos-fix i))))
  (defrule ordD-s_i
    (equal (ordD (s_i i v)) (acl2::pos-fix i))
    :use ((:instance result-1-6
                     (x (* (f v) (expt (D) (acl2::pos-fix i)))))
          (:instance result-1-5
                     (d (f v))
                     (r (acl2::pos-fix i))))
    :prep-lemmas
    ((acl2::with-arith5-nonlinear-help
      (defrule lemma
        (implies (and (rationalp f)
                      (posp i)
                      (<= (/ (D)) f))
                 (<= 1 (* f (expt (D) i))))
        :cases ((<= (D) (expt (D) i))))))))

(define t_i
  ((i posp)
   (v pos-rationalp))
  :returns (t_i (and (integerp t_i) (< 1 t_i))
                :rule-classes :type-prescription)
  (+ (s_i i v) 1)
  ///
  (fty::deffixequiv t_i)
  (defruled t_i-linear
    (let* ((t_i (t_i i v))
           (i (acl2::pos-fix i)))
      (and (< (expt (D) (- i 1)) t_i)
           (< (* (f v) (expt (D) i)) t_i)
           (<= t_i (expt (D) i))))
    :rule-classes :linear
    :use s_i-linear)
  (defrule ordD-t_i
    (implies (not (equal (t_i i v) (expt (D) (acl2::pos-fix i))))
             (equal (ordD (t_i i v)) (acl2::pos-fix i)))
    :cases ((integerp (expt (D) (acl2::pos-fix i))))
    :enable s_i-linear
    :use ((:instance result-1-3
                     (x (s_i i v))
                     (k (acl2::pos-fix i)))
          (:instance result-1-3
                     (x (t_i i v))
                     (k (acl2::pos-fix i))))))

(define u_i
   ((i posp)
    (v pos-rationalp))
   :returns (u pos-rationalp :rule-classes ())
   (let* ((i (acl2::pos-fix i))
          (s_i (s_i i v)))
     (* s_i (expt (D) (- (e v) i))))
   ///
   (fty::deffixequiv u_i)
   (acl2::with-arith5-nonlinear++-help
    (defruled u_i-linear
      (let* ((u_i (u_i i v))
             (e (e v))
             (i (acl2::pos-fix i))
             (v (pos-rational-fix v)))
        (and (<= (expt (D) (- e 1)) u_i)
             (< (- v (expt (D) (- e i))) u_i)
             (<= u_i v)
             (< u_i (expt (D) e))))
      :rule-classes ((:linear :trigger-terms ((u_i i v))))
      :enable f
      :use s_i-linear))
   (defrule ordD-u_i
     (equal (ordD (u_i i v))
            (ordD v))
     :enable (e result-1-5))
   (defrule has-D-length-u-i
     (has-D-length (u_i i v) i)
     :use (:instance has-D-length-suff
                     (r (- (e v) (acl2::pos-fix i)))
                     (d (s_i i v))))
   (acl2::with-arith5-help
    (defruled u_i-when-has-D-length
      (implies (has-D-length v i)
               (equal (u_i i v) (pos-rational-fix v)))
      :enable (has-D-length s_i f))))

(define w_i
   ((i posp)
    (v pos-rationalp))
   :returns (w pos-rationalp :rule-classes ())
   (let* ((i (acl2::pos-fix i))
          (t_i (t_i i v)))
     (* t_i (expt (D) (- (e v) i))))
   ///
   (fty::deffixequiv w_i)
   (acl2::with-arith5-help
    (defruled w_i-as-u_i
      (equal (w_i i v)
             (+ (u_i i v)
                (expt (D) (- (e v) (acl2::pos-fix i)))))
      :enable (u_i t_i)))
   (acl2::with-arith5-nonlinear++-help
    (defruled w_i-linear
      (let* ((w_i (w_i i v))
             (e (e v))
             (v (pos-rational-fix v)))
        (and (< (expt (D) (- e 1)) w_i)
             (< v w_i)
             (<= w_i (expt (D) e))))
      :rule-classes ((:linear :trigger-terms ((w_i i v))))
      :enable f
      :use t_i-linear))
   (acl2::with-arith5-help
   (defrule ordD-w_i
     (implies (not (= (w_i i v) (expt (D) (e v))))
              (equal (ordD (w_i i v))
                     (ordD v)))
     :enable (e result-1-5)
     :use (:instance ordD-t_i)))
   (acl2::with-arith5-help
    (defrule has-D-length-w-i
      (has-D-length (w_i i v) i)
      :cases ((= (t_i i v) (expt (D) (acl2::pos-fix i))))
      :hints
      (("subgoal 2" :use (:instance has-D-length-suff
                                    (r (- (e v) (acl2::pos-fix i)))
                                    (d (t_i i v))))
       ("subgoal 1" :in-theory (enable has-D-length f e))))))

(define algo1-measure
  ((i posp)
   (v pos-rationalp)
   (f formatp))
  :returns (measure natp :rule-classes ())
  (let ((i (acl2::pos-fix i))
        (n (+ 2 (- (e v) (e (MIN_VALUE f))))))
    (nfix (- n i)))
  ///
  (fty::deffixequiv algo1-measure)
  (acl2::with-arith5-help
   (defrule algo1-measure-lemma
     (implies (and (not (in-tau-intervalp (u_i i v) (Rv v f)))
                   (not (in-tau-intervalp (w_i i v) (Rv v f))))
              (< (algo1-measure (+ 1 (acl2::pos-fix i)) v f)
                 (algo1-measure i v f)))
     :rule-classes :linear
     :enable (w_i-as-u_i)
     :use ((:instance u-or-w-in-Rv
                      (u (u_i i v))
                      (w (w_i i v)))
           u_i-linear
           lemma1
           (:instance lemma2 (i (acl2::pos-fix i))))
     :prep-lemmas
     ((defruled lemma1
        (<= (MIN_VALUE f)
            (- (tau-interval-hi (Rv v f)) (tau-interval-lo (Rv v f))))
        :enable (width-Rv MIN_VALUE)
        :disable (tau-interval-lo tau-interval-hi))
      (defruled lemma2
        (let ((n (+ 2 (e v) (- (e (MIN_VALUE f))))))
          (implies (and (integerp i)
                        (>= i n))
                   (< (expt (D) (- (e v) i)) (MIN_VALUE f))))
        :enable e
        :use (:instance result-1-4
                        (x (MIN_VALUE F))
                        (y (expt (D) (+ (- i) (ordD v))))))))))

(define algo1
  ((from posp)
   (v pos-rationalp)
   (f formatp))
  :measure (algo1-measure from v f)
  :returns (mv (i posp :rule-classes :type-prescription)
               (dv pos-rationalp :rule-classes :type-prescription))
  (let* ((i (acl2::pos-fix from))
         (v (pos-rational-fix v))
         (f (format-fix f))
         (Rv (Rv v f))
         (u (u_i i v))
         (w (w_i i v))
         (u-last-digit (digitn (f u) (- i) (D))))
    (cond ((and (not (in-tau-intervalp u Rv))
                (not (in-tau-intervalp w Rv)))
           (algo1 (1+ i) v f))
          ((and (in-tau-intervalp u Rv)
                (not (in-tau-intervalp w Rv)))
           (mv i u))
          ((and (not (in-tau-intervalp u Rv))
                (in-tau-intervalp w Rv))
           (mv i w))
          ((< (- v u) (- w v)) (mv i u))
          ((> (- v u) (- w v)) (mv i w))
          ((evenp u-last-digit) (mv i u))
          (t (mv i w)))))

(rule ; Example 1
 (let* ((f (dp))
        (v (rne #f0.0811 (prec f))))
   (mv-let (i z) (algo1 1 v f)
     (and
      (= v #f0.081100000000000005417888360170763917267322540283203125)
      (= i 3)
      (= z #f0.0811))))
   :enable ((dp)))
