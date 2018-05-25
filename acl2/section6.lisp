(in-package "RTL")
(include-book "section5")

(local (include-book "rtl/rel11/support/basic" :dir :system))
(local (include-book "rtl/rel11/support/float" :dir :system))
(local (include-book "rtl/rel11/support/reps" :dir :system))
(local (acl2::allow-arith5-help))

(defruledl expt-natp
  (implies (and (radixp D)
                (natp i))
           (posp (expt D i)))
  :rule-classes :type-prescription)

(acl2::with-arith5-help
 (defruled has-D-length-c*2^q
   (implies (and (posp c)
                 (integerp q)
                 (radixp D)
                 (evenp D))
            (let* ((x (* c (expt 2 q)))
                   (factor (if (<= 0 q) (expt 2 q) (expt (/ D 2) (- q))))
                   (i (ordD D (* c factor))))
              (has-D-length x i D)))
   :use ((:instance has-D-length-suff
                    (r (if (<= 0 q) 0 q))
                    (d_ (* c (expt 2 q) (expt D (if (<= 0 q) 0 (- q))))))
         (:instance lemma (half-D (/ D 2))))
   :prep-lemmas
   ((defruled lemma
      (implies (and (integerp q)
                    (< q 0)
                    (posp half-D))
               (integerp (* (expt 2 q) (expt (* 2 half-D) (- q)))))))))

(defrule has-D-length-when-finite-positive-binary
  (implies (and (finite-positive-binary-p v f)
                (radixp D)
                (evenp D))
           (let* ((q (q v f))
                  (c (c v f))
                  (factor (if (<= 0 q) (expt 2 q) (expt (/ D 2) (- q))))
                  (i (ordD D (* c factor))))
             (has-D-length v i D)))
  :use ((:instance finite-positive-binary-necc
                   (x v))
        (:instance has-D-length-c*2^q
                   (c (c v f))
                   (q (q v f)))))

(local
 (acl2::with-arith5-help
  (defrule s_i-lemma
    (implies (and (posp i)
                  (radixp D))
             (and (<= (expt D (1- i)) (fl (* (f v D) (expt D i))))
                  (< (fl (* (f v D) (expt D i))) (expt D i))))
    :use (:instance result-1-1
                    (x (* (f v D) (expt D i)))
                    (m (expt D (1- i)))
                    (n (expt D i))))))

(define s_i
  ((i posp)
   (v pos-rationalp)
   (D radixp))
  :returns (s_i posp :rule-classes :type-prescription
                :hints (("goal" :in-theory (e/d (expt-natp) (expt))
                         :use ((:instance expt-natp
                                          (D (radix-fix D))
                                          (i (1- (acl2::pos-fix i))))
                               (:instance s_i-lemma
                                          (D (radix-fix D))
                                          (i (acl2::pos-fix i)))))))
  (fl (* (f v D) (expt (radix-fix D) (acl2::pos-fix i))))
  ///
  (fty::deffixequiv s_i)
  (defruled s_i-linear
    (let* ((s_i (s_i i v D))
           (i (acl2::pos-fix i))
           (D (radix-fix D)))
      (and (<= (expt D (- i 1)) s_i)
           (< (1- (* (f v D) (expt D i))) s_i)
           (<= s_i (* (f v D) (expt D i)))
           (< s_i (expt D i))))
    :rule-classes ((:linear :trigger-terms ((s_i i v D))))
    :use (:instance s_i-lemma
                    (D (radix-fix D))
                    (i (acl2::pos-fix i))))
  (acl2::with-arith5-help
   (defrule ordD-s_i
     (equal (ordD D (s_i i v D)) (acl2::pos-fix i))
     :use ((:instance result-1-6
                      (x (* (f v d) (expt (radix-fix D) (acl2::pos-fix i)))))
           (:instance result-1-5
                      (d_ (f v d))
                      (D (radix-fix D))
                      (r (acl2::pos-fix i))))
     :prep-lemmas
     ((acl2::with-arith5-nonlinear-help
       (defrule lemma
         (implies (and (rationalp f)
                       (radixp D)
                       (posp i)
                       (<= (/ D) f))
                  (<= 1 (* f (expt D i))))
         :cases ((<= D (expt D i)))))))))

(define t_i
  ((i posp)
   (v pos-rationalp)
   (D radixp))
  :returns (t_i (and (integerp t_i) (< 1 t_i))
                :rule-classes :type-prescription)
  (+ (s_i i v D) 1)
  ///
  (fty::deffixequiv t_i)
  (acl2::with-arith5-help
   (defruled t_i-linear
     (let* ((t_i (t_i i v D))
            (i (acl2::pos-fix i))
            (D (radix-fix D)))
       (and (< (expt D (- i 1)) t_i)
            (< (* (f v D) (expt D i)) t_i)
            (<= t_i (expt D i))))
     :rule-classes :linear
     :use s_i-linear
     :enable (radix-fix expt-natp)))
  (acl2::with-arith5-nonlinear-help
   (defrule ordD-t_i
     (implies (not (equal (t_i i v D) (expt (radix-fix D) (acl2::pos-fix i))))
              (equal (ordD D (t_i i v D)) (acl2::pos-fix i)))
     :cases ((integerp (expt (radix-fix D) (acl2::pos-fix i))))
     :enable s_i-linear
     :use ((:instance result-1-3
                      (x (s_i i v D))
                      (k (acl2::pos-fix i)))
           (:instance result-1-3
                      (x (t_i i v D))
                      (k (acl2::pos-fix i)))))))

(acl2::with-arith5-help
 (define u_i
   ((i posp)
    (v pos-rationalp)
    (D radixp))
   :returns (u pos-rationalp :rule-classes :type-prescription
               :hints (("goal" :in-theory (enable pos-rationalp))))
   (let* ((i (acl2::pos-fix i))
          (D (radix-fix D))
          (s_i (s_i i v D)))
     (* s_i (expt D (- (e v D) i))))
   ///
   (fty::deffixequiv u_i)
   (defruled u_i-linear
     (let* ((u_i (u_i i v D))
            (e (e v D))
            (i (acl2::pos-fix i))
            (v (pos-rational-fix v))
            (D (radix-fix D)))
       (and (<= (expt D (- e 1)) u_i)
            (< (- v (expt D (- e i))) u_i)
            (<= u_i v)
            (< u_i (expt D e))))
     :rule-classes ((:linear :trigger-terms ((u_i i v D))))
     :use (:instance lemma (D (radix-fix D)))
     :prep-lemmas
     ((acl2::with-arith5-nonlinear++-help
       (defrule lemma
         (let* ((u_i (u_i i v D))
                (e (e v D))
                (v (pos-rational-fix v))
                )
           (implies (radixp D)
                    (and (<= (expt D (- e 1)) u_i)
                         (< (- v (expt D (- e (acl2::pos-fix i)))) u_i)
                         (<= u_i v)
                         (< u_i (expt D e)))))
         :enable f
         :use s_i-linear))))
   (defrule ordD-u_i
     (equal (ordD D (u_i i v D))
            (ordD D v))
     :enable e
     :use (:instance result-1-5
                     (d_ (s_i i v D))
                     (r (- (e v D) (acl2::pos-fix i)))
                     (D (radix-fix D))))
   (defrule has-D-length-u-i
     (has-D-length (u_i i v D) i D)
     :use (:instance has-D-length-suff
                     (D (radix-fix D))
                     (r (- (e v d) (acl2::pos-fix i)))
                     (d_ (s_i i v d))))
   (defruled u_i-when-has-D-length
     (implies (has-D-length v i D)
              (equal (u_i i v D) (pos-rational-fix v)))
     :enable (has-D-length s_i f))))

(acl2::with-arith5-help
 (define w_i
   ((i posp)
    (v pos-rationalp)
    (D radixp))
   :returns (w pos-rationalp :rule-classes :type-prescription
               :hints (("goal" :in-theory (enable pos-rationalp))))
   (let* ((i (acl2::pos-fix i))
          (D (radix-fix D))
          (t_i (t_i i v D)))
     (* t_i (expt D (- (e v D) i))))
   ///
   (fty::deffixequiv w_i)
   (defruled w_i-as-u_i
     (equal (w_i i v D)
            (+ (u_i i v D)
               (expt (radix-fix D) (- (e v D) (acl2::pos-fix i)))))
     :enable (u_i t_i))
   (defruled w_i-linear
     (let* ((w_i (w_i i v D))
            (e (e v D))
            (v (pos-rational-fix v))
            (D (radix-fix D)))
       (and (< (expt D (- e 1)) w_i)
            (< v w_i)
            (<= w_i (expt D e))))
     :rule-classes ((:linear :trigger-terms ((w_i i v D))))
     :use (:instance lemma (D (radix-fix D)))
     :prep-lemmas
     ((acl2::with-arith5-nonlinear++-help
       (defrule lemma
         (let* ((w_i (w_i i v D))
                (e (e v D)))
           (implies (radixp D)
                    (and (< (expt D (- e 1)) w_i)
                         (< (pos-rational-fix v) w_i)
                         (<= w_i (expt D e)))))
         :enable f
         :use t_i-linear))))
   (defrule ordD-w_i
     (implies (not (= (w_i i v D) (expt (radix-fix D) (e v D))))
              (equal (ordD D (w_i i v D))
                     (ordD D v)))
     :enable e
     :use ((:instance ordD-t_i)
           (:instance result-1-5
                      (d_ (t_i i v D))
                      (r (- (e v D) (acl2::pos-fix i)))
                      (D (radix-fix D)))))
   (acl2::with-arith5-help
   (defrule has-D-length-w-i
     (has-D-length (w_i i v D) i D)
     :cases ((= (t_i i v D) (expt (radix-fix D) (acl2::pos-fix i))))
     :hints
     (("subgoal 2" :use (:instance has-D-length-suff
                                   (D (radix-fix D))
                                   (r (- (e v d) (acl2::pos-fix i)))
                                   (d_ (t_i i v d))))
      ("subgoal 1" :in-theory (enable pos-rational-fix has-D-length f e)
       :use (:instance expt-natp
                       (D (radix-fix D))
                       (i (1- (acl2::pos-fix i))))))))))

(acl2::with-arith5-help
 (define algo1-measure
   ((i posp)
    (v pos-rationalp)
    (f formatp)
    (D radixp))
   :returns (measure natp)
   (let ((i (acl2::pos-fix i))
         (n (+ 2 (- (e v D) (e (MIN_VALUE f) D)))))
     (nfix (- n i)))
   ///
   (fty::deffixequiv algo1-measure)
   (acl2::with-arith5-help
    (defrule algo1-measure-lemma
      (implies (and (not (in-tau-intervalp (u_i i v D) (Rv v f)))
                    (not (in-tau-intervalp (w_i i v D) (Rv v f))))
               (< (algo1-measure (+ 1 (acl2::pos-fix i)) v f D)
                  (algo1-measure i v f D)))
      :rule-classes :linear
      :enable (w_i-as-u_i)
      :use ((:instance u-or-w-in-Rv
                       (u (u_i i v D))
                       (w (w_i i v D)))
            u_i-linear
            lemma1
            (:instance lemma2
                       (D (radix-fix D))
                       (i (acl2::pos-fix i))))
      :prep-lemmas
      ((defrule pos-rationalp-expt-when-radixp
         (implies (radixp D)
                  (and (pos-rationalp (expt D k))
                       (< 0 (expt D k))))
         :rule-classes (:rewrite :type-prescription))
       (defruled lemma1
         (<= (MIN_VALUE f)
             (- (tau-interval-hi (Rv v f)) (tau-interval-lo (Rv v f))))
         :enable (width-Rv MIN_VALUE)
         :disable (tau-interval-lo tau-interval-hi))
       (defruled lemma2
         (let ((n (+ 2 (e v D) (- (e (MIN_VALUE f) D)))))
           (implies (and (radixp D)
                         (integerp i)
                         (>= i n))
                    (< (expt D (- (e v D) i)) (MIN_VALUE f))))
         :enable e
         :use (:instance result-1-4
                         (x (MIN_VALUE F))
                         (y (expt D (+ (- i) (ordD D v)))))))))))

(define algo1
  ((from posp)
   (v pos-rationalp)
   (f formatp)
   (D radixp))
  :measure (algo1-measure from v f D)
  :returns (mv (i posp :rule-classes :type-prescription)
               (dv pos-rationalp :rule-classes :type-prescription))
  (let* ((i (acl2::pos-fix from))
         (v (pos-rational-fix v))
         (f (format-fix f))
         (D (radix-fix D))
         (Rv (Rv v f))
         (u (u_i i v D))
         (w (w_i i v D))
         (u-last-digit (mod (s_i i v D) D)))
    (cond ((and (not (in-tau-intervalp u Rv))
                (not (in-tau-intervalp w Rv)))
           (algo1 (1+ i) v f D))
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
   (mv-let (i z) (algo1 1 v f 10)
     (and
      (= v #f0.081100000000000005417888360170763917267322540283203125)
      (= i 3)
      (= z #f0.0811))))
   :enable ((dp)))
