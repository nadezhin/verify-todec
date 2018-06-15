(in-package "RTL")
(include-book "section6")

(local (include-book "rtl/rel11/support/basic" :dir :system))
(local (include-book "rtl/rel11/support/bits" :dir :system))
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

(defruled algo1-i<=max-from-i-j
  (implies (and (in-tau-intervalp (pos-rational-fix d) (Rv v f))
                (has-D-length d j))
           (<= (algo1-i from-i v f) (max (acl2::pos-fix from-i)
                                         (acl2::pos-fix j))))
 :enable (in-tau-intervalp-i<=j<<algo1-i
          algo1-i has-D-length-monotone)
 :use (:instance uninteresting-other-than-u_i-w_i
                 (d (pos-rational-fix d))
                 (i (max (acl2::pos-fix from-i) (acl2::pos-fix j)))))

(defruled has-minimal-D-length-algo1
  (implies (and (in-tau-intervalp d (Rv v f))
                (pos-rationalp d)
                (posp from-i)
                (integerp j)
                (<= from-i j)
                (< j (algo1-i from-i v f)))
           (not (has-D-length d j)))
  :use algo1-i<=max-from-i-j)

(acl2::with-arith5-help
 (defruled evenp-when-evenp-last-digit
  (implies (integerp i)
           (equal (evenp (mod i (D)))
                  (evenp i)))
  :enable D))

(acl2::with-arith5-help
 (defruled evenp-digitn-f-u_i
  (implies (posp i)
           (equal (evenp (digitn (f (u_i i v)) (- i) (D)))
                  (evenp (s_i i v))))
  :enable (f-u_i digitn-def evenp-when-evenp-last-digit)
  :disable evenp))

(acl2::with-arith5-help
 (defruled evenp-digitn-f-w_i
   (implies (and (integerp i)
                 (<= 2 i))
            (equal (evenp (digitn (f (w_i i v)) (- i) (D)))
                   (evenp (t_i i v))))
   :enable (f-w_i digitn-def evenp-when-evenp-last-digit)
   :disable evenp
   :cases ((= (t_i i v) (expt (D) i)))
   :hints (("subgoal 1" :in-theory (enable w_i f e)))
   :prep-lemmas
   ((defrule lemma
      (implies (posp i)
               (evenp (expt (D) i)))
      :enable ((D))
      :expand (expt 10 i)
      :disable acl2::normalize-factors-gather-exponents))))

(acl2::with-arith5-help
 (defruled evenp-digitn-f-w_i-as-digitn-f-u_i
   (implies (and (integerp i)
                 (<= 2 i))
            (equal (evenp (digitn (f (w_i i v)) (- i) (D)))
                   (not (evenp (digitn (f (u_i i v)) (- i) (D))))))

   :enable (evenp-digitn-f-u_i
            evenp-digitn-f-w_i)
   :disable evenp
   :prep-lemmas
   ((defrule lemma
      (equal (evenp (s_i i v))
             (not (evenp (t_i i v))))
      :enable t_i))))

; Previos theorem would be incorrect for i=1
(rule
 (let ((i 1)
       (v #f9.5))
   (and (= (u_i i v) 9)
        (= (w_i i v) 10)
        (= (f (u_i i v)) #f0.9)
        (= (f (w_i i v)) #f0.1)
        (= (digitn (f (u_i i v)) (- i) (D)) 9)
        (= (digitn (f (w_i i v)) (- i) (D)) 1)
        (not (evenp (digitn (f (u_i i v)) (- i) (D))))
        (not (evenp (digitn (f (w_i i v)) (- i) (D))))))
 :enable ((D)))

(defruled algo1-satisfies-specs
   (let ((dv (algo1 from-i v f))
         (i (algo1-i from-i v f)))
     (implies (and (in-tau-intervalp d (Rv v f))
                   (has-D-length d j)
                   (pos-rationalp d)
                   (pos-rationalp v)
                   (not (= d dv))
                   (integerp from-i)
                   (<= 2 from-i)
                   (integerp j)
                   (<= from-i j))
              (or (< i j)
                  (and (= i j)
                       (< (abs (- dv v)) (abs (- d v))))
                  (and (= i j)
                       (= (abs (- dv v)) (abs (- d v)))
                       (evenp (digitn (f dv) (- i) (D)))
                       (not (evenp (digitn (f d) (- j) (D))))))))
   :enable (evenp-digitn-f-w_i-as-digitn-f-u_i
            u_i-linear w_i-linear)
   :disable (evenp abs)
   :use (:instance uninteresting-other-than-u_i-w_i
                   (i j))
   :cases ((= j (algo1-i from-i v f)))
   :hints (("subgoal 2" :use (:instance in-tau-intervalp-i<=j<<algo1-i
                                        (i from-i)))
           ("subgoal 1" :in-theory (enable algo1 abs))))
