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

(defconst *alpha* 17/12)

(defrule frac-alpha-i<2
  (implies (and (posp i)
                (< i 2))
           (let ((frac (frac (* *alpha* i))))
             (and (<= 5/12 frac)
                  (<= frac 5/12)))))

(defruled frac-alpha-i<3
  (implies (and (posp i)
                (< i 3))
           (let ((frac (frac (* *alpha* i))))
             (and (<= 5/12 frac)
                  (<= frac 5/6))))
  :cases ((< i 2)
          (= i 2)
          (> i 2)))

(defruled frac-alpha-i<5
  (implies (and (posp i)
                (< i 5))
           (let ((frac (frac (* *alpha* i))))
             (and (<= 1/4 frac)
                  (<= frac 5/6))))
  :cases ((< i 3)
          (= i 3)
          (> i 3))
  :hints (("subgoal 3" :use frac-alpha-i<3)))

(defruled frac-alpha-i<7
  (implies (and (posp i)
                (< i 7))
           (let ((frac (frac (* *alpha* i))))
             (and (<= 1/12 frac)
                  (<= frac 5/6))))
  :cases ((< i 5)
          (= i 5)
          (> i 5))
  :hints (("subgoal 3" :use frac-alpha-i<5)))

(acl2::with-arith5-help
 (defruled frac-alpha-i<12
  (implies (and (posp i)
                (< i 12))
           (let ((frac (frac (* *alpha* i))))
             (and (<= 1/12 frac)
                  (<= frac 11/12))))
  :cases ((< i 7)
          (= i 7)
          (> i 7))
  :hints (("subgoal 3" :use frac-alpha-i<7)
          ("subgoal 1" :use ((:instance frac-alpha-i<5
                                        (i (- i 7)))
                             (:instance frac-+
                                        (x (* *alpha* 7))
                                        (y (* *alpha* (- i 7)))))))))

(acl2::with-arith5-help
 (defrule frac-alpha-thm
   (implies (natp i)
            (let ((frac (frac (* *alpha* i))))
             (implies (not (= frac 0))
                      (and (<= 1/12 frac)
                           (<= frac 11/12)))))
   :use (:instance lemma
                   (i (floor i 12))
                   (j (mod i 12)))
   :prep-lemmas
   ((defrule lemma
      (implies (and (natp i)
                    (natp j)
                    (< j 12))
               (let* ((k (+ (* i 12) j))
                      (frac (frac (* *alpha* k))))
                 (implies (not (= frac 0))
                          (and (<= 1/12 frac)
                               (<= frac 11/12)))))
      :use ((:instance frac-alpha-i<12
                       (i j))
            (:instance frac-+
                       (x (* *alpha* i 12))
                       (y (* *alpha* j))))))))

