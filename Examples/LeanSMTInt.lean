/-
These are examples borrowed from the SMT Lean tests,
`https://github.com/ufmg-smite/lean-smt/blob/main/Test/Int`
-/
import Mathlib.Data.Real.Basic
import Auto.Tactic

-- Arith

example (n m : Int) (h : 0 < m) : n % m < m := by
  --smt [h]
  sorry

example (n m k l : Int) : (n - m) * k + l = n*k - m*k + l := by
  --smt
  sorry

example (n m k l : Int) (hN : n ≤ m) (hK : k ≤ l) : n + k ≤ m + l := by
  --smt [hN, hK]
  sorry

-- Cong

theorem cong (x y : Int) (f : Int → Int) : x = y → f x = f y := by
  auto

-- DefineSort

def MyInt := Int
def MyInt.add (a b : MyInt) : MyInt := Int.add a b

example (a b : MyInt) : a.add b = b.add a := by
  sorry

-- Dvd

opaque dvd : Int → Int → Bool

example
    (a b c d e : Int)
    (dvdax : ∀ x y z, dvd x y → dvd y z → dvd x z)
    (h1 : dvd a b)
    (h2 : dvd b c)
    (h3 : dvd c d)
    (h4 : dvd d e) :
  dvd a e := by
    have h5 : dvd a c := by
      -- smt [h1, h2, dvdax]
      exact dvdax _ _ _ h1 h2
    have h6 : dvd c e := by
      -- smt [h3, h4, dvdax]
      exact dvdax _ _ _ h3 h4
    -- smt [h5, h6, dvdax]
    exact dvdax _ _ _ h5 h6

-- ForallExists

theorem forallExists : ∀ x : Nat, ∃ y : Int, x ≤ y := by
  -- smt
  intro x
  apply Exists.intro
  case w => exact Int.ofNat x
  case h =>
    induction x with
    | zero => decide
    | succ x _ =>
        simp only [LE.le, Int.le, HSub.hSub, Sub.sub, Int.sub, Neg.neg,
                   Int.neg, Int.negOfNat, HAdd.hAdd, Add.add, Int.add]
        simp only [Int.subNatNat, Nat.sub_self, Int.NonNeg.mk]

-- Let

section
variable (f : Int → Int)

example (h : f 10 = 10) : let y := 10; f y = 10 := by
  auto

example (h : let y := 10; f y = 10) : f 10 = 10 := by
  auto

example (h : f 10 = 10) : f 10 = 10 := by
  auto

theorem neg (x : Int) : - -x = x := by
  sorry



end