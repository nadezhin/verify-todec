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
                  (pos-rationalp d))
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
  (implies (and (in-tau-intervalp (pos-rational-fix d) (Rv v f))
                (has-D-length d j))
           (<= (algo1-i from v f) (max (acl2::pos-fix from)
                                       (acl2::pos-fix j))))
 :enable (in-tau-intervalp-i<=j<<algo1-i
          algo1-i has-D-length-monotone)
 :use (:instance uninteresting-other-than-u_i-w_i
                 (d (pos-rational-fix d))
                 (i (max (acl2::pos-fix from) (acl2::pos-fix j)))))

(defruled has-minimal-D-length-algo1
  (implies (and (in-tau-intervalp d (Rv v f))
                (pos-rationalp d)
                (posp from)
                (integerp j)
                (<= from j)
                (< j (algo1-i from v f)))
           (not (has-D-length d j)))
  :use i<=max-from-j-algo1)

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

(defruled algo1-satisfies-specs
   (let ((dv (algo1 from v f))
         (i (algo1-i from v f)))
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
   :enable (u_i-linear w_i-linear)
   :disable (evenp abs)
   :use (:instance uninteresting-other-than-u_i-w_i
                   (i j))
   :cases ((= j (algo1-i from v f)))
   :hints (("subgoal 2" :use (:instance in-tau-intervalp-i<=j<<algo1-i
                                        (i from)))
           ("subgoal 1" :in-theory (enable algo1 abs))))
