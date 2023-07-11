; From Mathlib/RingTheory/Polynomial/Chebyshev.lean/T_add_two
(declare-fun T (Int) Real)
(declare-const x Real)
(assert (= (T 0) 1))
(assert (= (T 1) x))
(assert (forall ((n Int)) (= (T (+ n 2)) (- (* 2 (* x (T (+ n 1)))) (T n)))))
(assert (not (= (T 2) (- (* 2 (* x x)) 1))))
(check-sat)