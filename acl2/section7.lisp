#|
(include-book "rtl/rel11/portcullis" :dir :system)
|#
(in-package "RTL")
(include-book "section6")

(local (include-book "rtl/rel11/support/basic" :dir :system))
(local (include-book "rtl/rel11/support/float" :dir :system))
(local (include-book "rtl/rel11/support/reps" :dir :system))
(local (acl2::allow-arith5-help))

(defrule i>=from-algo1
  (let ((i (mv-nth 0 (algo1 from v f D))))
    (<= (acl2::pos-fix from) i))
  :rule-classes :linear
  :enable algo1)

(defrule dv-in-Rv-algo1
  (let ((dv (mv-nth 1 (algo1 from v f D))))
    (in-tau-intervalp dv (Rv v f)))
  :enable algo1)

(defrule algo1-u_i-or-v_i
  (mv-let (i dv) (algo1 from v f D)
    (or (= dv (u_i i v D))
        (= dv (w_i i v D))))
  :rule-classes ()
  :enable algo1)

(defrule has-D-length-algo1
  (mv-let (i dv) (algo1 from v f D)
    (has-D-length dv i D))
  :use algo1-u_i-or-v_i)

(defruled ordD-between-u_i-w_i
 (let ((u_i (u_i i v D))
       (w_i (w_i i v D)))
   (implies (and (has-D-length x i D)
                 (pos-rationalp x)
                 (<= u_i x)
                 (< x w_i))
            (equal (ordD D x)
                   (ordD D v))))
 :enable (e u_i-linear w_i-linear)
 :use (:instance result-1-3 (k (ordD D v))))

(defruled not-has-D-length-between-u_i-w_i
  (let ((u_i (u_i i v D))
        (w_i (w_i i v D)))
    (implies (and (< u_i (pos-rational-fix x))
                  (< (pos-rational-fix x) w_i))
             (not (has-D-length x i D))))
  :use (:instance lemma
                  (i (acl2::pos-fix i))
                  (D (radix-fix D))
                  (x (pos-rational-fix x)))
  :prep-lemmas
  ((acl2::with-arith5-nonlinear++-help
    (defrule lemma
      (let ((u_i (u_i i v D))
            (w_i (w_i i v D)))
        (implies (and (posp i)
                      (radixp D)
                      (pos-rationalp x)
                      (< u_i x)
                      (< x w_i))
                 (not (has-D-length x i D))))
      :enable (has-D-length u_i w_i t_i f e)
      :use ((:instance lemma1
                       (s (s_i i v D))
                       (x (* x (expt D (- i (e x D))))))
            (:instance ordD-between-u_i-w_i))
      :prep-lemmas
      ((defruled lemma1
         (implies (and (integerp s)
                       (< s x)
                       (< x (1+ s)))
                  (not (integerp x)))))))))

(defruled in-tau-intervalp-u_i-or-w_i-when-in-tau-intervalp-has-D-length
  (let ((Rv (Rv v f))
        (u_i (u_i i v D))
        (w_i (w_i i v D)))
    (implies (and (not (in-tau-intervalp u_i Rv))
                  (not (in-tau-intervalp w_i Rv))
                  (has-D-length d_ i D)
                  (pos-rationalp d_)
                  (not (= d_ u_i))
                  (not (= d_ w_i)))
             (not (in-tau-intervalp d_ Rv))))
  :cases ((and (< (u_i i v D) d_) (< d_ (w_i i v D))))
  :hints (("subgoal 1" :use (:instance not-has-D-length-between-u_i-w_i (x d_)))
          ("subgoal 2" :in-theory (enable in-tau-intervalp
                                          tau-interval-lo
                                          tau-interval-hi
                                          Rv u_i-linear w_i-linear))))

(defruled has-minimal-D-length-algo1
 (mv-let (i dv) (algo1 from v f D)
   (declare (ignore dv))
   (implies (and (in-tau-intervalp d_ (Rv v f))
                 (pos-rationalp d_)
                 (posp from)
                 (integerp j)
                 (<= from j)
                 (< j i))
             (not (has-D-length d_ j D))))
 :induct (algo1 from v f D)
 :enable algo1
 :hints
 (("subgoal *1/1" :use
   (:instance in-tau-intervalp-u_i-or-w_i-when-in-tau-intervalp-has-D-length
              (i from)))))
#|
(mv-let (i dv) (algo1 2 (* 4048 (MIN_VALUE (dp))) (dp) 10)
  (list
   i
   dv
   (* (f dv 10) (expt 10 i))
   (- (e dv 10) i)))

(acl2::with-arith5-help
 (rule
  (mv-let (i dv) (algo1 from v f D)
    (implies (and (in-tau-intervalp d_ (Rv v f))
                  (has-D-length d_ i D)
                  (pos-rationalp v)
                  (pos-rationalp d_)
                  (not (= v d_)))
             (<= (abs (- dv v))(abs (- d_ v)))))
 ))
|#
