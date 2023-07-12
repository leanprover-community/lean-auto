import Mathlib.Tactic.Polyrith

/--
def polyrith_test₁
    (x y z : ℚ)
    (H₁ : x + y = z + x) : y * y = z * z := by polyrith

-- Succeeds with
--   Try this: linear_combination (y + z) * H₁
-/

def polyrith_test₁
    (x y z : ℚ)
    (H₁ : x + y = z + x) : y * y = z * z := by linear_combination (y + z) * H₁