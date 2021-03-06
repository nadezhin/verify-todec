(in-package "RTL")
(include-book "section5")

(local (include-book "rtl/rel11/support/basic" :dir :system))
(local (include-book "rtl/rel11/support/bits" :dir :system))
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

(local
 (acl2::with-arith5-help
  (defruled evenp-when-evenp-last-digit
    (implies (integerp i)
             (equal (evenp (mod i (D)))
                    (evenp i)))
    :enable D)))

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
      :enable (has-D-length s_i f)))
   (acl2::with-arith5-help
    (defruled f-u_i
      (equal (f (u_i i v))
             (* (s_i i v) (expt (D) (- (acl2::pos-fix i)))))
      :enable (f e result-1-5)))
   (acl2::with-arith5-help
    (defruled evenp-digitn-f-u_i
      (implies (= -i (- (acl2::pos-fix i)))
               (equal (evenp (digitn (f (u_i i v)) -i (D)))
                      (evenp (s_i i v))))
      :enable (f-u_i digitn-def evenp-when-evenp-last-digit)
      :disable (evenp u_i))))

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
     :use ordD-t_i))
   (acl2::with-arith5-help
    (defrule has-D-length-w-i
      (has-D-length (w_i i v) i)
      :cases ((= (t_i i v) (expt (D) (acl2::pos-fix i))))
      :hints
      (("subgoal 2" :use (:instance has-D-length-suff
                                    (r (- (e v) (acl2::pos-fix i)))
                                    (d (t_i i v))))
       ("subgoal 1" :in-theory (enable has-D-length f e)))))
   (acl2::with-arith5-help
    (defruled f-w_i
      (implies (not (= (t_i i v) (expt (D) (acl2::pos-fix i))))
               (equal (f (w_i i v))
                      (* (t_i i v) (expt (D) (- (acl2::pos-fix i))))))
      :enable (f e result-1-5)
      :use ordD-t_i))
    (acl2::with-arith5-help
     (defruled evenp-digitn-f-w_i
       (implies (= -i (- (acl2::pos-fix i)))
                (equal (evenp (digitn (f (w_i i v)) -i (D)))
                       (and (evenp (t_i i v))
                            (or (< 1 (acl2::pos-fix i))
                                (not (= (t_i i v) (D)))))))
       :enable (f-w_i digitn-def evenp-when-evenp-last-digit)
       :disable (evenp w_i)
       :cases ((= (t_i i v) (expt (D) (acl2::pos-fix i))))
       :hints (("subgoal 1" :in-theory (enable w_i f e)))
       :prep-lemmas
       ((defrule lemma
          (implies (posp i)
                   (evenp (expt (D) i)))
          :enable ((D))
          :expand (expt 10 i)
          :disable acl2::normalize-factors-gather-exponents)))))


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
     :enable (w_i-as-u_i wid-Rv>=MIN_VALUE)
     :use ((:instance u-or-w-in-Rv
                      (u (u_i i v))
                      (w (w_i i v)))
           u_i-linear
           (:instance lemma (i (acl2::pos-fix i))))
     :prep-lemmas
     ((defruled lemma
        (let ((n (+ 2 (e v) (- (e (MIN_VALUE f))))))
          (implies (and (integerp i)
                        (>= i n))
                   (< (expt (D) (- (e v) i)) (MIN_VALUE f))))
        :enable e
        :use (:instance result-1-4
                        (x (MIN_VALUE F))
                        (y (expt (D) (+ (- i) (ordD v))))))))))

(define algo1-i
  ((i posp)
   (v pos-rationalp)
   (f formatp))
  :measure (algo1-measure i v f)
  :returns (i posp :rule-classes ())
  (let ((i (acl2::pos-fix i)))
    (if (and (not (in-tau-intervalp (u_i i v) (Rv v f)))
             (not (in-tau-intervalp (w_i i v) (Rv v f))))
        (algo1-i (+ i 1) v f)
      i))
  ///
  (fty::deffixequiv algo1-i)
  (defrule algo1-i-linear
    (>= (algo1-i i v f) (acl2::pos-fix i))
    :rule-classes :linear)
  (defruled in-tau-intervalp-algo1-i
    (let ((i (algo1-i i v f)))
      (and (implies (not (in-tau-intervalp (u_i i v) (Rv v f)))
                    (in-tau-intervalp (w_i i v) (Rv v f)))
           (implies (not (in-tau-intervalp (w_i i v) (Rv v f)))
                    (in-tau-intervalp (u_i i v) (Rv v f))))))
  (defruled in-tau-intervalp-i<=j<algo1-i
    (implies (and (<= (acl2::pos-fix i) (acl2::pos-fix j))
                  (< (acl2::pos-fix j) (algo1-i i v f)))
             (and (not (in-tau-intervalp (u_i j v) (Rv v f)))
                  (not (in-tau-intervalp (w_i j v) (Rv v f)))))
    :induct (algo1-i i v f)
    :disable acl2::pos-equiv
    :hints (("subgoal *1/1" :use (:instance acl2::pos-equiv$inline
                                            (x j)
                                            (y i)))))
  (defruled algo1-i-when-u_i-or-w_i-in-tau-intrvalp
    (implies (or (in-tau-intervalp (u_i i v) (Rv v f))
                 (in-tau-intervalp (w_i i v) (Rv v f)))
             (equal (algo1-i i v f) (acl2::pos-fix i)))))

(define algo1
  ((from-i posp)
   (v pos-rationalp)
   (f formatp))
  :returns (dv pos-rationalp :rule-classes ())
  (let* ((i (algo1-i from-i v f))
         (v (pos-rational-fix v))
         (f (format-fix f))
         (Rv (Rv v f))
         (u (u_i i v))
         (w (w_i i v))
         (u-last-digit (digitn (f u) (- i) (D))))
    (cond ((and (in-tau-intervalp u Rv) (not (in-tau-intervalp w Rv))) u)
          ((and (not (in-tau-intervalp u Rv)) (in-tau-intervalp w Rv)) w)
          ((< (abs (- v u)) (abs (- w v))) u)
          ((> (abs (- v u)) (abs (- w v))) w)
          ((evenp u-last-digit) u)
          (t w)))
  ///
  (fty::deffixequiv algo1)
  (defruled algo1-is-u_i-or-w_i
    (let* ((dv (algo1 from-i v f))
           (i (algo1-i from-i v f))
           (u (u_i i v))
           (w (w_i i v)))
      (and (implies (not (= dv u)) (equal dv w))
           (implies (not (= dv w)) (equal dv u)))))
  (defrule in-tau-intervalp-algo1
    (in-tau-intervalp (algo1 from-i v f) (Rv v f))
    :enable in-tau-intervalp-algo1-i)
  (defrule has-D-length-algo1
    (has-D-length (algo1 from-i v f) (algo1-i from-i v f)))
  (defrule algo1-next-when-not-in-tau-intervalp-u_i-and-w_i
    (implies (and (not (in-tau-intervalp (u_i i v) (Rv v f)))
                  (not (in-tau-intervalp (w_i i v) (rv v f)))
                  (posp i))
             (equal (algo1 (1+ i) v f)
                    (algo1 i v f)))
    :cases ((= (algo1-i i v f) (algo1-i (1+ i) v f)))
    :hints (("subgoal 2" :in-theory (disable algo1)
             :expand (algo1-i i v f))
            ("subgoal 1" :in-theory (enable algo1))))
  (acl2::with-arith5-help
   (defruled algo1-when-in-tau-intervalp-u_i-or-w_i
     (let* ((ui (u_i i v))
            (wi (w_i i v))
            (Rv (Rv v f))
            (signum (signum (+ (* 2 (pos-rational-fix v)) (- ui) (- wi)))))
       (implies (and (or (in-tau-intervalp ui Rv)
                         (in-tau-intervalp wi Rv)))
                (equal (algo1 i v f)
                       (cond
                        ((not (in-tau-intervalp wi Rv)) ui)
                        ((not (in-tau-intervalp ui Rv)) wi)
                        ((< signum 0) ui)
                        ((> signum 0) wi)
                        ((evenp (s_i i v)) ui)
                        (t wi)))))
     :enable (algo1-i-when-u_i-or-w_i-in-tau-intrvalp
              algo1 signum u_i-linear w_i-linear)
     :use (:instance evenp-digitn-f-u_i
                     (-i (- (acl2::pos-fix i)))))))

(rule ; Example 1
 (let* ((f (dp))
        (v (rne #f0.0811 (prec f)))
        (from-i 1))
   (and
    (= v #f0.081100000000000005417888360170763917267322540283203125)
    (= (algo1-i from-i v f) 3)
    (= (algo1 from-i v f) #f0.0811)))
 :enable ((dp)))

