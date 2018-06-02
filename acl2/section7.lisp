#|
(include-book "rtl/rel11/portcullis" :dir :system)
|#
(in-package "RTL")
(include-book "section6")

(local (include-book "rtl/rel11/support/basic" :dir :system))
(local (include-book "rtl/rel11/support/bits" :dir :system))
(local (include-book "rtl/rel11/support/float" :dir :system))
(local (include-book "rtl/rel11/support/reps" :dir :system))
(local (acl2::allow-arith5-help))

(defrule i>=from-algo1
  (let ((i (mv-nth 0 (algo1 from v f))))
    (<= (acl2::pos-fix from) i))
  :rule-classes :linear
  :enable algo1)

(defruled algo1-as-choose-u_i-w_i
  (mv-let (i dv) (algo1 from v f)
    (equal dv (choose-u_i-w_i i v f)))
  :enable algo1)

(defruled choose-u_i-w_i-thm
  (implies (not (equal (choose-u_i-w_i i v f) (u_i i v)))
           (equal (choose-u_i-w_i i v f) (w_i i v)))
  :enable choose-u_i-w_i)

(defrule dv-in-Rv-algo1
  (let ((dv (mv-nth 1 (algo1 from v f))))
    (in-tau-intervalp dv (Rv v f)))
  :use algo1-as-choose-u_i-w_i
  :enable (algo1 choose-u_i-w_i))

(defrule algo1-u_i-or-v_i
  (mv-let (i dv) (algo1 from v f)
    (or (= dv (u_i i v))
        (= dv (w_i i v))))
  :rule-classes ()
  :enable (algo1 choose-u_i-w_i-thm))

(defrule has-D-length-algo1
  (mv-let (i dv) (algo1 from v f)
    (has-D-length dv i))
  :use algo1-u_i-or-v_i)

(defruled ordD-between-u_i-w_i
 (let ((u_i (u_i i v))
       (w_i (w_i i v)))
   (implies (and (has-D-length x i)
                 (<= u_i (pos-rational-fix x))
                 (< (pos-rational-fix x) w_i))
            (equal (ordD x)
                   (ordD v))))
 :enable (e u_i-linear w_i-linear)
 :use (:instance result-1-3 (k (ordD v))))

(acl2::with-arith5-nonlinear++-help
 (defruled not-has-D-length-between-u_i-w_i
  (let ((u_i (u_i i v))
        (w_i (w_i i v)))
    (implies (and (< u_i (pos-rational-fix x))
                  (< (pos-rational-fix x) w_i))
             (not (has-D-length x i))))
  :enable (has-D-length u_i w_i t_i f e)
  :use ((:instance lemma1
                   (s (s_i i v))
                   (x (* (pos-rational-fix x)
                         (expt (D) (- (acl2::pos-fix i) (e x))))))
        ordD-between-u_i-w_i)
  :prep-lemmas
  ((defruled lemma1
     (implies (and (integerp s)
                   (< s x)
                   (< x (1+ s)))
              (not (integerp x)))))))

(defrule uninteresting-other-than-u_i-w_i
  (let ((Rv (Rv v f))
        (u_i (u_i i v))
        (w_i (w_i i v)))
    (implies (and (in-tau-intervalp d Rv)
                  (has-D-length d i)
                  (pos-rationalp d)
                  (pos-rationalp v)
                  (not (= d u_i))
                  (not (= d w_i)))
             (or (and (in-tau-intervalp u_i Rv)
                      (< d u_i))
                 (and (in-tau-intervalp w_i Rv)
                      (< w_i d)))))
  :rule-classes ()
  :cases ((and (< (u_i i v) d)
               (< d (w_i i v))))
  :hints
  (("subgoal 2" :in-theory (enable in-tau-intervalp
                                   tau-interval-lo
                                   tau-interval-hi
                                   Rv u_i-linear w_i-linear))
   ("subgoal 1" :use (:instance not-has-D-length-between-u_i-w_i (x d)))))

(defrule uninteresting-other-than-u_i-w_i-alt
  (let ((Rv (Rv v f))
        (u_i (u_i i v))
        (w_i (w_i i v)))
    (implies (and (in-tau-intervalp d Rv)
                  (has-D-length d i)
                  (pos-rationalp d)
                  (pos-rationalp v))
             (or (and (in-tau-intervalp u_i Rv)
                      (<= d u_i))
                 (and (in-tau-intervalp w_i Rv)
                      (<= w_i d)))))
  :rule-classes ()
  :cases ((and (< (u_i i v) d)
               (< d (w_i i v))))
  :hints
  (("subgoal 2" :in-theory (enable in-tau-intervalp
                                   tau-interval-lo
                                   tau-interval-hi
                                   Rv u_i-linear w_i-linear))
   ("subgoal 1" :use (:instance not-has-D-length-between-u_i-w_i (x d)))))


(defruled i<=max-from-j-algo1
 (let ((i (mv-nth 0 (algo1 from v f))))
   (implies (and (in-tau-intervalp (pos-rational-fix d) (Rv v f))
                 (has-D-length d j))
            (<= i (max (acl2::pos-fix from) (acl2::pos-fix j)))))
 :rule-classes ((:linear :trigger-terms ((mv-nth 0 (algo1 from v f)))))
 :induct (algo1 from v f)
 :enable algo1
 :hints
 (("subgoal *1/2":use
   ((:instance uninteresting-other-than-u_i-w_i
              (d (pos-rational-fix d))
              (v (pos-rational-fix v))
              (i (acl2::pos-fix from)))
    (:instance has-D-length-monotone
               (x d)
               (i j)
               (j from))))))

(defruled has-minimal-D-length-algo1
 (mv-let (i dv) (algo1 from v f)
   (declare (ignore dv))
   (implies (and (in-tau-intervalp d (Rv v f))
                 (pos-rationalp d)
                 (posp from)
                 (integerp j)
                 (<= from j)
                 (< j i))
             (not (has-D-length d j))))
 :induct (algo1 from v f)
 :enable algo1
 :hints (("subgoal *1/2" :use
          (:instance uninteresting-other-than-u_i-w_i
                     (v (pos-rational-fix v))
                     (i from)))))
#|
(acl2::with-arith5-help
 (defruled algo1-meets-specs
   (mv-let (i dv) (algo1 from v f)
     (implies (and (in-tau-intervalp d (Rv v f))
                 (has-D-length d j)
                 (pos-rationalp d)
                 (pos-rationalp v)
                 (not (= d dv))
                 (integerp from)
                 (<= 2 from)
                 (integerp j)
                 (<= from j))
            (or (< i j)
                (and (= i j)
                     (< (abs (- dv v)) (abs (- d v))))
                (and (= i j)
                     (= (abs (- dv v)) (abs (- d v)))
                     (evenp (digitn (f dv) (- i) (D)))
                     (not (evenp (digitn (f d) (- j) (D))))))))
   :enable (;algo1
            choose-u_i-w_i
                  u_i-linear w_i-linear)
 :disable evenp
 :do-not-induct t
 :use (algo1-as-choose-u_i-w_i
       (:instance uninteresting-other-than-u_i-w_i
                  (i (mv-nth 0 (algo1 from v f)))
                  )
       (:instance has-D-length-monotone
                  (x d)
                  (i j)
                  (j (mv-nth 0 (algo1 from v f))))
       )))
|#
(acl2::with-arith5-help
 (defrule evenp-digitn-f-w_i
   (implies (and (integerp from)
                 (<= 2 from))
            (equal (evenp (digitn (f (w_i from v)) (- from) (D)))
                   (not (evenp (digitn (f (u_i from v)) (- from) (D))))))
   :cases ((= (t_i from v) (expt (D) from)))
   :enable (f e u_i w_i result-1-5 digitn-def ordD-t_i)
   :disable evenp
   :prep-lemmas
   ((defrule lemma
      (equal (evenp (mod (s_i i v) (D)))
             (not (evenp (mod (t_i i v) (D)))))
      :enable t_i))))

(acl2::with-arith5-help
 (defruled algo1-meets-specs
   (mv-let (i dv) (algo1 from v f)
     (implies (and (in-tau-intervalp d (Rv v f))
                 (has-D-length d j)
                 (pos-rationalp d)
                 (pos-rationalp v)
                 (not (= d dv))
                 (integerp from)
                 (<= 2 from)
                 (integerp j)
                 (<= from j))
            (or (< i j)
                (and (= i j)
                     (< (abs (- dv v)) (abs (- d v))))
                (and (= i j)
                     (= (abs (- dv v)) (abs (- d v)))
                     (evenp (digitn (f dv) (- i) (D)))
                     (not (evenp (digitn (f d) (- j) (D))))))))
 :induct (algo1 from v f)
 :enable (algo1 u_i-linear w_i-linear)
 :disable evenp
 :hints
 (("subgoal *1/2" :in-theory (enable choose-u_i-w_i)
    :use (:instance uninteresting-other-than-u_i-w_i
                    (i from)))
  ("subgoal *1/1" :in-theory (enable choose-u_i-w_i)
   :use
   (algo1-as-choose-u_i-w_i
    (:instance uninteresting-other-than-u_i-w_i
               (i (mv-nth 0 (algo1 from v f)))
               ))))))

(defruled in-tau-intervalp-u_i-or-w_i-when-in-tau-intervalp-has-D-length
  (let ((Rv (Rv v f))
        (u_i (u_i i v))
        (w_i (w_i i v)))
    (implies (and (not (in-tau-intervalp u_i Rv))
                  (not (in-tau-intervalp w_i Rv))
                  (has-D-length d i)
                  (pos-rationalp d)
                  (not (= d u_i))
                  (not (= d w_i)))
             (not (in-tau-intervalp d Rv))))
  :cases ((and (< (u_i i v) (pos-rational-fix d))
               (< (pos-rational-fix d) (w_i i v))))
  :hints (("subgoal 1" :use (:instance not-has-D-length-between-u_i-w_i (x d)))
          ("subgoal 2" :in-theory (enable in-tau-intervalp
                                          tau-interval-lo
                                          tau-interval-hi
                                          Rv u_i-linear w_i-linear))))

#|
(mv-let (i dv) (algo1 2 (* 3 (MIN_VALUE (dp))) (dp))
  (list
   i
   dv
   (* (f dv) (expt 10 i))
   (- (e dv) i)))

(acl2::with-arith5-help
 (rule
  (mv-let (i dv) (algo1 from v f)
    (implies (and (in-tau-intervalp d (Rv v f))
                  (has-D-length d i)
                  (pos-rationalp v)
                  (pos-rationalp d)
                  (not (= v d)))
             (<= (abs (- dv v))(abs (- d v)))))
 ))
|#
