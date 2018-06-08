#|
(include-book "rtl/rel11/portcullis" :dir :system)
|#
(in-package "RTL")
(include-book "section10")

(local (include-book "rtl/rel11/support/float" :dir :system))
(local (include-book "std/basic/inductions" :dir :system))
(local (acl2::allow-arith5-help))

(acl2::with-arith5-help
 (define !s_i
  ((i posp)
   (v pos-rationalp)
   (f formatp))
  :returns (!s_i posp :rule-classes :type-prescription)
  (let ((i (min (H f) (acl2::pos-fix i))))
    (* (s_i i v) (expt (D) (- (H f) i))))
  ///
  (fty::deffixequiv !s_i)
  (acl2::with-arith5-nonlinear++-help
   (defruled !s_i-linear
     (let* ((!s_i (!s_i i v f))
            (H (H f)))
       (implies (and (posp i)
                     (<= i H))
                (and (<= (expt (D) (- H 1)) !s_i)
                     (< (- (* (f v) (expt (D) H)) (expt (D) (- H i)))
                        !s_i)
                     (<= !s_i (* (f v) (expt (D) H)))
                     (< !s_i (expt (D) H)))))
     :rule-classes ((:linear :trigger-terms ((!s_i i v f))))
     :use s_i-linear))
  (defrule ordD-!s_i
    (implies (and (posp i)
                  (<= i (H f)))
             (equal (ordD (!s_i i v f)) (H f)))
    :enable result-1-5)))

(acl2::with-arith5-help
 (define !t_i
  ((i posp)
   (v pos-rationalp)
   (f formatp))
  :returns (!t_i posp :rule-classes :type-prescription)
  (let ((i (min (H f) (acl2::pos-fix i))))
    (* (t_i i v) (expt (D) (- (H f) i))))
  ///
  (fty::deffixequiv !t_i)
  (acl2::with-arith5-nonlinear++-help
   (defruled !t_i-linear
     (let* ((!t_i (!t_i i v f))
            (H (H f)))
       (implies (and (posp i)
                     (<= i H))
                (and (< (expt (D) (- H 1)) !t_i)
                     (< (* (f v) (expt (D) H)) !t_i)
                     (<= !t_i (expt (D) H)))))
     :rule-classes ((:linear :trigger-terms ((!t_i i v f))))
     :use t_i-linear))
  (defrule ordD-!t_i
    (implies (and (posp i)
                  (<= i (H f))
                  (not (equal (!t_i i v f) (expt (D) (H f)))))
             (equal (ordD (!t_i i v f)) (H f)))
    :use ordD-t_i
    :enable result-1-5)))

(acl2::with-arith5-help
 (defruled !s_i-as-!s_H
   (let ((H (H f)))
     (implies (and (posp i)
                   (< i H))
              (equal (!s_i i v f)
                     (* (fl (/ (!s_i H v f) (expt (D) (- H i))))
                        (expt (D) (- H i))))))
   :enable (!s_i s_i)
   :use (:instance fl/int-rewrite
                   (x (* (f v) (expt (D) (H f))))
                   (n (expt (D) (- (H f) i))))))

(define !q
  ((v pos-rationalp)
   (f formatp))
  :returns (!q integerp :rule-classes ())
  (let ((q (q v f))
        (c (c v f)))
    (if (or (= q (Qmin f)) (not (= c (2^{P-1} f))))
        (- q 1)
      (- q 2)))
  ///
  (fty::deffixequiv !q))

(define !c
  ((v pos-rationalp)
   (f formatp))
  :returns (!c pos-rationalp :rule-classes ())
  (let ((q (q v f))
        (c (c v f)))
    (if (or (= q (Qmin f)) (not (= c (2^{P-1} f))))
        (* 2 c)
      (* 4 c)))
  ///
  (fty::deffixequiv !c)
  (defrule !c-linear
    (<= (!c v f) (* 4 (2^{P-1} f)))
    :rule-classes :linear)
  (defrule !c-type-when-finite-positive-binary
    (implies (finite-positive-binary-p v f)
             (and (integerp (!c v f))
                  (< 1 (!c v f))))
    :rule-classes :type-prescription)
  (acl2::with-arith5-help
   (defrule !c*2^!q-as-v
     (equal (* (!c v f) (expt 2 (!q v f)))
            (pos-rational-fix v))
     :enable (!q c))))

(define !cr
  ((v pos-rationalp)
   (f formatp))
  :returns (!cr pos-rationalp :rule-classes ())
  (let ((q (q v f))
        (c (c v f)))
    (if (or (= q (Qmin f)) (not (= c (2^{P-1} f))))
        (+ (!c v f) 1)
      (+ (!c v f) 2)))
  ///
  (fty::deffixequiv !cr)
  (defrule !cr-linear
    (<= (!cr v f) (+ 2 (* 4 (2^{P-1} f))))
    :rule-classes :linear)
  (defrule !cr-type-when-finite-positive-binary
    (implies (finite-positive-binary-p v f)
             (and (integerp (!cr v f))
                  (< 1 (!cr v f))))
    :rule-classes :type-prescription)
  (acl2::with-arith5-help
   (defrule !cr*2^!q-as-vr
     (equal (* (!cr v f) (expt 2 (!q v f)))
            (vr v f))
     :enable (!q !c c vr))))

(define !cl
  ((v pos-rationalp)
   (f formatp))
  :returns (!cl rationalp :rule-classes ())
  (- (!c v f) 1)
  ///
  (fty::deffixequiv !cl)
  (defrule !cl-linear
    (<= (!cl v f) (+ -1 (* 4 (2^{P-1} f))))
    :rule-classes :linear)
  (defrule !cl-type-when-finite-positive-binary
    (implies (finite-positive-binary-p v f)
             (posp (!cl v f)))
    :rule-classes :type-prescription)
  (acl2::with-arith5-help
   (defrule !cl*2^!q-as-vl
     (equal (* (!cl v f) (expt 2 (!q v f)))
            (vl v f))
     :enable (!q !c vl-alt))))

(acl2::with-arith5-help
 (define S
   ((v pos-rationalp)
    (f formatp))
   :returns (S pos-rationalp :rule-classes ())
   (let ((e (e v))
         (H (H f))
         (!q (!q v f)))
     (if (> e H)
         (expt 2 (- H e)) ; XL or L
       (if (>= (+ H (- e) !q) 0)
           (expt (D) (- H e)) ; M
         (* (expt 2 (- !q)) (expt (D/2) (- H e)))))) ; XS or S
   ///
   (fty::deffixequiv S)))

(acl2::with-arith5-help
 (define T_
   ((v pos-rationalp)
    (f formatp))
   :returns (T_ pos-rationalp :rule-classes ())
   (/ (expt (D) (- (H f) (e v))) (S v f))
   ///
   (fty::deffixequiv T_)))

(define !v
  ((v pos-rationalp)
   (f formatp))
  :returns (!v pos-rationalp :rule-classes ())
  (* (pos-rational-fix v) (S v f))
  ///
  (fty::deffixequiv !v))

(define !vl
  ((v pos-rationalp)
   (f formatp))
  :returns (!vl rationalp :rule-classes ())
  (* (vl v f) (S v f))
  ///
  (fty::deffixequiv !vl))

(define !vr
  ((v pos-rationalp)
   (f formatp))
  :returns (!vr pos-rationalp :rule-classes ())
  (* (vr v f) (S v f))
  ///
  (fty::deffixequiv !vr))

(define !u_i
  ((i posp)
   (v pos-rationalp)
   (f formatp))
  :returns (!vr pos-rationalp :rule-classes ())
  (* (u_i i v) (S v f))
  ///
  (fty::deffixequiv !u_i))

(define !w_i
  ((i posp)
   (v pos-rationalp)
   (f formatp))
  :returns (!vr pos-rationalp :rule-classes ())
  (* (w_i i v) (S v f))
  ///
  (fty::deffixequiv !w_i))

(defruled result-7-part-1-dp
  (let* ((f (dp))
         (H (H f))
         (e (e v)))
    (implies (and (pos-rationalp v)
                  (< v (MIN_NORMAL f)))
             (<= e H)))
  :enable (e (dp))
  :use (:instance result-1-4
                  (x v)
                  (y (MIN_NORMAL (dp)))))

(defruled result-7-part-2-dp
  (let* ((f (dp))
         (H (H f))
         (e (e v))
         (!q (!q v f)))
    (implies (and (finite-positive-binary-p v f)
                  (< v (MIN_NORMAL f)))
             (< (+ H (- e) !q) 0)))
  :enable (e !q (dp))
  :use ((:instance finite-positive-binary-necc
                   (x v)
                   (f (dp)))
        (:instance c-vs-MIN_NORMAL
                   (x v)
                   (f (dp)))
        (:instance result-1-4
                   (x (MIN_VALUE (dp)))
                   (y v))))
#|
(acl2::with-arith5-help
 (defrule case-impossible-dp
   (let* ((f (dp))
          (H (H f))
          (e (e v))
          (!q (!q v f)))
     (implies (and (pos-rationalp v)
                   (< (- H e) 0))
              (>= (+ (- H e) !q) 0)))
   :enable (e !q q expq (dp))
   :cases ((>= v #f1e17))
   :hints
   (("subgoal 2" :use (:instance result-1-3
                                 (x v)
                                 (k (ordD v))))
    )

   ))
   :use (:instance result-1-4
                   (x v)
                   (y (expt (D) 17)))
   :hints
   (("subgoal 8'''" :in-theory (enable (D))
     :use (:instance expe-monotone
                                 (b 2)
                                 (x 0)
                                 (y v)))
    )
;   :enable (e !q q expq (dp))
;   :use ((:instance result-1-3
;                    (x v)
;                    (k (ordD v)))
         )
   ))


(let* ((f (dp))
       (H (H f))
       (v (expt (D) H))
       (e (e v))
       (!q (!q v f)))
  (list
   :v v
   :e e
   :q !q))
    (implies (and (pos-rationalp v)
                  (< (- H e) 0))
             (>= (+ (- H e) !q) 0)))
|#
