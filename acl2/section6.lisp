#|
(include-book "rtl/rel11/portcullis" :dir :system)
|#
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
           (< s_i (expt D i))))
    :rule-classes :linear
    :use (:instance s_i-lemma
                    (D (radix-fix D))
                    (i (acl2::pos-fix i)))))

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
           (<= t_i (expt D i))))
    :rule-classes :linear
    :enable (s_i-linear radix-fix expt-natp))))

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
   (defrule u_i-linear
     (let* ((u_i (u_i i v D))
            (e (e v D))
            (D (radix-fix D)))
       (and (<= (expt D (- e 1)) u_i)
            (< u_i (expt D e))))
     :rule-classes :linear
     :use (:instance lemma (D (radix-fix D)))
     :prep-lemmas
     ((acl2::with-arith5-nonlinear-help
       (defrule lemma
         (let* ((u_i (u_i i v D))
                (e (e v D)))
           (implies (radixp D)
                    (and (<= (expt D (- e 1)) u_i)
                         (< u_i (expt D e)))))
         :use s_i-linear))))))

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
   (defrule w_i-linear
     (let* ((w_i (w_i i v D))
            (e (e v D))
            (D (radix-fix D)))
       (and (< (expt D (- e 1)) w_i)
            (<= w_i (expt D e))))
     :rule-classes :linear
     :use (:instance lemma (D (radix-fix D)))
     :prep-lemmas
     ((acl2::with-arith5-nonlinear-help
       (defrule lemma
         (let* ((w_i (w_i i v D))
                (e (e v D)))
           (implies (radixp D)
                    (and (< (expt D (- e 1)) w_i)
                         (<= w_i (expt D e)))))
         :use t_i-linear))))))

(define algo1-aux
  ((i posp)
   (n posp)
   (v pos-rationalp)
   (vint tau-intervalp)
   (D radixp))
  :measure (nfix (- n i))
  (let ((u (u_i i v D))
        (w (w_i i v D)))
    (cond ((and (not (in-tau-intervalp u vint))
                (not (in-tau-intervalp w vint)))
           (and (posp (- n i))
                (algo1-aux (1+ i) n v vint D)))
          ((and (in-tau-intervalp u vint)
                (not (in-tau-intervalp w vint)))
           u)
          ((and (not (in-tau-intervalp u vint))
                (in-tau-intervalp w vint))
           w)
          ((< (- v u) (- w v)) u)
          ((> (- v u) (- w v)) w)
          ((integerp (* (f u D) (expt D i) 1/2)) u)
          (t w))))

(define algo1
  ((v pos-rationalp)
   (f formatp)
   (D radixp))
  (algo1-aux 1 (bias f)  v (Rv v f) D))

(rule ; Example 1
 (let* ((f (dp))
        (v (rne #f0.0811 (prec f)))
        (z (algo1 v f 10)))
 (and
  (= v #f0.081100000000000005417888360170763917267322540283203125)
  (= z #f0.0811)))
 :enable ((dp)))
