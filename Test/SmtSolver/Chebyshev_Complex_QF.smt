; From Mathlib/RingTheory/Polynomial/Chebyshev.lean/T_add_two
; Unsound embedding, succeeds
(set-option :produce-proofs true)
(declare-fun T (Int) Real)
(declare-const x Real)
(declare-const m Int)
(declare-const k Int)

; T_add_two R m
(assert (= (T (+ m 2)) (- (* 2 (* x (T (+ m 1)))) (T m))))

; T_add_two R k
(assert (= (T (+ k 2)) (- (* 2 (* x (T (+ k 1)))) (T k))))

; T_add_two R (2 * m + k + 2)
(assert (= (T (+ (+ (* 2 m) (+ k 2)) 2)) (- (* 2 (* x (T (+ (+ (* 2 m) (+ k 2)) 1)))) (T (+ (* 2 m) (+ k 2))))))

; mul_T m (k + 2)
(assert (forall ((k Int)) (= (* 2 (* (T m) (T (+ m (+ k 2))))) (+ (T (+ (* 2 m) (+ k 2))) (T (+ k 2))))))
; mul_T (m + 1) (k + 1)
(assert (forall ((k Int)) (= (* 2 (* (T (+ m 1)) (T (+ (+ m 1) (+ k 1))))) (+ (T (+ (* 2 (+ m 1)) (+ k 1))) (T (+ k 1))))))

; not (type_of (mul_T m (k + 2)))
(assert (not (= (* 2 (* (T (+ m 2)) (T (+ (+ m 2) k)))) (+ (T (+ (* 2 (+ m 2)) k)) (T k)))))

(check-sat)
(get-proof)