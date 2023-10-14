; From Mathlib/Analysis/Hofer.lean/hofer
; reformulation: ε * ϕ x ≤ ε / 2 ^ k * ϕ x' ↔ 2 ^ k * ϕ x ≤ ϕ x'
(set-option :produce-proofs true)
(declare-const e Real)
(declare-const px Real)
(declare-const px2 Real)
(declare-const pk Real)
(assert (xor (<= (* e px) (* (/ e pk) px2)) (<= (* pk px) px2)))
(assert (< 0 e))
(assert (< 0 pk))
(check-sat)
(get-proof)