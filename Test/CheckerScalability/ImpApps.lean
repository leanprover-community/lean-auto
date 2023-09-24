import Auto.Tactic

set_option profiler true

partial def chopList (s : List α) (n : Nat) : List (List α) :=
  if n == 0 then
    [s]
  else
    if s.length < n then
      [s]
    else
      s.take n :: chopList (s.drop n) n

def test₁ (n : Nat) : String :=
  let types := (List.range (n + 1)).map (fun n => s!"(α{n} : Prop)")
  let types := (chopList types 5).map (String.intercalate " ")
  let begin := "(β : Type) (G : α0)"
  let impFacts := (List.range n).map (fun n => s!"(H{n} : ∃ (x : β), α{n} → α{n + 1})")
  let impFacts := (chopList impFacts 2).map (String.intercalate " ")
  let allDecls := types ++ begin :: impFacts
  let exbody := "  " ++ String.intercalate "\n  " allDecls
  "example\n" ++ exbody ++ s!" : α{n} := by auto"

#eval IO.println (test₁ 60)

-- 1s
set_option maxRecDepth 2000 in
example
  (α0 : Prop) (α1 : Prop) (α2 : Prop) (α3 : Prop) (α4 : Prop)
  (α5 : Prop) (α6 : Prop) (α7 : Prop) (α8 : Prop) (α9 : Prop)
  (α10 : Prop) (α11 : Prop) (α12 : Prop) (α13 : Prop) (α14 : Prop)
  (α15 : Prop) (α16 : Prop) (α17 : Prop) (α18 : Prop) (α19 : Prop)
  (α20 : Prop) (α21 : Prop) (α22 : Prop) (α23 : Prop) (α24 : Prop)
  (α25 : Prop) (α26 : Prop) (α27 : Prop) (α28 : Prop) (α29 : Prop)
  (α30 : Prop) (α31 : Prop) (α32 : Prop) (α33 : Prop) (α34 : Prop)
  (α35 : Prop) (α36 : Prop) (α37 : Prop) (α38 : Prop) (α39 : Prop)
  (α40 : Prop) (α41 : Prop) (α42 : Prop) (α43 : Prop) (α44 : Prop)
  (α45 : Prop) (α46 : Prop) (α47 : Prop) (α48 : Prop) (α49 : Prop)
  (α50 : Prop) (α51 : Prop) (α52 : Prop) (α53 : Prop) (α54 : Prop)
  (α55 : Prop) (α56 : Prop) (α57 : Prop) (α58 : Prop) (α59 : Prop)
  (α60 : Prop)
  (β : Type) (G : α0)
  (H0 : ∃ (x : β), α0 → α1) (H1 : ∃ (x : β), α1 → α2)
  (H2 : ∃ (x : β), α2 → α3) (H3 : ∃ (x : β), α3 → α4)
  (H4 : ∃ (x : β), α4 → α5) (H5 : ∃ (x : β), α5 → α6)
  (H6 : ∃ (x : β), α6 → α7) (H7 : ∃ (x : β), α7 → α8)
  (H8 : ∃ (x : β), α8 → α9) (H9 : ∃ (x : β), α9 → α10)
  (H10 : ∃ (x : β), α10 → α11) (H11 : ∃ (x : β), α11 → α12)
  (H12 : ∃ (x : β), α12 → α13) (H13 : ∃ (x : β), α13 → α14)
  (H14 : ∃ (x : β), α14 → α15) (H15 : ∃ (x : β), α15 → α16)
  (H16 : ∃ (x : β), α16 → α17) (H17 : ∃ (x : β), α17 → α18)
  (H18 : ∃ (x : β), α18 → α19) (H19 : ∃ (x : β), α19 → α20)
  (H20 : ∃ (x : β), α20 → α21) (H21 : ∃ (x : β), α21 → α22)
  (H22 : ∃ (x : β), α22 → α23) (H23 : ∃ (x : β), α23 → α24)
  (H24 : ∃ (x : β), α24 → α25) (H25 : ∃ (x : β), α25 → α26)
  (H26 : ∃ (x : β), α26 → α27) (H27 : ∃ (x : β), α27 → α28)
  (H28 : ∃ (x : β), α28 → α29) (H29 : ∃ (x : β), α29 → α30)
  (H30 : ∃ (x : β), α30 → α31) (H31 : ∃ (x : β), α31 → α32)
  (H32 : ∃ (x : β), α32 → α33) (H33 : ∃ (x : β), α33 → α34)
  (H34 : ∃ (x : β), α34 → α35) (H35 : ∃ (x : β), α35 → α36)
  (H36 : ∃ (x : β), α36 → α37) (H37 : ∃ (x : β), α37 → α38)
  (H38 : ∃ (x : β), α38 → α39) (H39 : ∃ (x : β), α39 → α40)
  (H40 : ∃ (x : β), α40 → α41) (H41 : ∃ (x : β), α41 → α42)
  (H42 : ∃ (x : β), α42 → α43) (H43 : ∃ (x : β), α43 → α44)
  (H44 : ∃ (x : β), α44 → α45) (H45 : ∃ (x : β), α45 → α46)
  (H46 : ∃ (x : β), α46 → α47) (H47 : ∃ (x : β), α47 → α48)
  (H48 : ∃ (x : β), α48 → α49) (H49 : ∃ (x : β), α49 → α50)
  (H50 : ∃ (x : β), α50 → α51) (H51 : ∃ (x : β), α51 → α52)
  (H52 : ∃ (x : β), α52 → α53) (H53 : ∃ (x : β), α53 → α54)
  (H54 : ∃ (x : β), α54 → α55) (H55 : ∃ (x : β), α55 → α56)
  (H56 : ∃ (x : β), α56 → α57) (H57 : ∃ (x : β), α57 → α58)
  (H58 : ∃ (x : β), α58 → α59) (H59 : ∃ (x : β), α59 → α60)
   : α60 := by auto