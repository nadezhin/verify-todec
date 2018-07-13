#|
(include-book "rtl/rel11/portcullis" :dir :system)
|#
(in-package "RTL")
(include-book "fty-lemmas")

(local (include-book "rtl/rel11/support/basic" :dir :system))
(local (acl2::allow-arith5-help))

(define frac
   ((x real/rationalp))
   :returns (frac (and (real/rationalp frac)
                       (<= 0 frac)
                       (< frac 1))
                  :rule-classes :type-prescription)
   (re (realfix x))
   ///
   (fty::deffixequiv frac)
   (defrule frac-int
     (implies (integerp x)
              (equal (frac x) 0)))
   (acl2::with-arith5-help
    (defruled frac-+
      (implies (and (real/rationalp x)
                    (real/rationalp y))
               (equal (frac (+ x y))
                      (if (< (+ (frac x) (frac y)) 1)
                          (+ (frac x) (frac y))
                        (+ -1 (frac x) (frac y)))))
      :enable fl)))

(defconst *alpha* 43/33)

#|
Output from net.java.jinterval.text2interval.fractions.Fractions:

alpha = 43/33
 = 1 + 1/(3 + 1/(3 + 1/(3)))
 1/1 4/3 13/10 43/33
frac(alpha*1) = 10/33
0 < i < 2 ==> 10/33 <= frac(alpha*i) <= 10/33
frac(alpha*2) = 20/33
0 < i < 3 ==> 10/33 <= frac(alpha*i) <= 20/33
frac(alpha*3) = 10/11
0 < i < 4 ==> 10/33 <= frac(alpha*i) <= 10/11
frac(alpha*4) = 7/33
0 < i < 7 ==> 7/33 <= frac(alpha*i) <= 10/11
frac(alpha*7) = 4/33
0 < i < 10 ==> 4/33 <= frac(alpha*i) <= 10/11
frac(alpha*10) = 1/33
0 < i < 13 ==> 1/33 <= frac(alpha*i) <= 10/11
frac(alpha*13) = 31/33
0 < i < 23 ==> 1/33 <= frac(alpha*i) <= 31/33
frac(alpha*23) = 32/33
0 < i < 33 ==> 1/33 <= frac(alpha*i) <= 32/33
frac(alpha*33) = 0
|#

(defrule frac-alpha-i<2
  (implies (and (posp i)
                (< i 2))
           (let ((frac (frac (* *alpha* i))))
             (and (<= 10/33 frac)
                  (<= frac 10/33)))))

(defruled frac-alpha-i<3
  (implies (and (posp i)
                (< i 3))
           (let ((frac (frac (* *alpha* i))))
             (and (<= 10/33 frac)
                  (<= frac 20/33))))
  :cases ((< i 2)
          (= i 2)
          (> i 2)))

(defruled frac-alpha-i<4
  (implies (and (posp i)
                (< i 4))
           (let ((frac (frac (* *alpha* i))))
             (and (<= 10/33 frac)
                  (<= frac 10/11))))
  :cases ((< i 3)
          (= i 3)
          (> i 3))
  :hints (("subgoal 3" :use frac-alpha-i<3)))

(acl2::with-arith5-help
 (defruled frac-alpha-i<7
   (implies (and (posp i)
                 (< i 7))
            (let ((frac (frac (* *alpha* i))))
              (and (<= 7/33 frac)
                   (<= frac 10/11))))
   :cases ((< i 4)
           (= i 4)
           (> i 4))
   :hints (("subgoal 3" :use frac-alpha-i<4)
           ("subgoal 1" :use ((:instance frac-alpha-i<3
                                         (i (- i 4)))
                              (:instance frac-+
                                         (x (* *alpha* 4))
                                         (y (* *alpha* (- i 4)))))))))

(acl2::with-arith5-help
 (defruled frac-alpha-i<10
   (implies (and (posp i)
                 (< i 10))
            (let ((frac (frac (* *alpha* i))))
              (and (<= 4/33 frac)
                   (<= frac 10/11))))
   :cases ((< i 7)
           (= i 7)
           (> i 7))
   :hints (("subgoal 3" :use frac-alpha-i<7)
           ("subgoal 1" :use ((:instance frac-alpha-i<3
                                         (i (- i 7)))
                              (:instance frac-+
                                         (x (* *alpha* 7))
                                         (y (* *alpha* (- i 7)))))))))

(acl2::with-arith5-help
 (defruled frac-alpha-i<13
   (implies (and (posp i)
                 (< i 13))
            (let ((frac (frac (* *alpha* i))))
              (and (<= 1/33 frac)
                   (<= frac 10/11))))
   :cases ((< i 10)
           (= i 10)
           (> i 10))
   :hints (("subgoal 3" :use frac-alpha-i<10)
           ("subgoal 1" :use ((:instance frac-alpha-i<3
                                         (i (- i 10)))
                              (:instance frac-+
                                         (x (* *alpha* 10))
                                         (y (* *alpha* (- i 10)))))))))

(acl2::with-arith5-help
 (defruled frac-alpha-i<23
  (implies (and (posp i)
                (< i 23))
           (let ((frac (frac (* *alpha* i))))
             (and (<= 1/33 frac)
                  (<= frac 31/33))))
  :cases ((< i 13)
          (= i 13)
          (> i 13))
  :hints (("subgoal 3" :use frac-alpha-i<13)
          ("subgoal 1" :use ((:instance frac-alpha-i<10
                                        (i (- i 13)))
                             (:instance frac-+
                                        (x (* *alpha* 13))
                                        (y (* *alpha* (- i 13)))))))))

(acl2::with-arith5-help
 (defruled frac-alpha-i<33
  (implies (and (posp i)
                (< i 33))
           (let ((frac (frac (* *alpha* i))))
             (and (<= 1/33 frac)
                  (<= frac 32/33))))
  :cases ((< i 23)
          (= i 23)
          (> i 23))
  :hints (("subgoal 3" :use frac-alpha-i<23)
          ("subgoal 1" :use ((:instance frac-alpha-i<10
                                        (i (- i 23)))
                             (:instance frac-+
                                        (x (* *alpha* 23))
                                        (y (* *alpha* (- i 23)))))))))

(acl2::with-arith5-help
 (defrule frac-alpha-thm
   (implies (natp i)
            (let ((frac (frac (* *alpha* i))))
             (implies (not (= frac 0))
                      (and (<= 1/33 frac)
                           (<= frac 32/33)))))
   :use (:instance lemma
                   (i (floor i 33))
                   (j (mod i 33)))
   :prep-lemmas
   ((defrule lemma
      (implies (and (natp i)
                    (natp j)
                    (< j 33))
               (let* ((k (+ (* i 33) j))
                      (frac (frac (* *alpha* k))))
                 (implies (not (= frac 0))
                          (and (<= 1/33 frac)
                               (<= frac 32/33)))))
      :use ((:instance frac-alpha-i<33
                       (i j))
            (:instance frac-+
                       (x (* *alpha* i 33))
                       (y (* *alpha* j))))))))

