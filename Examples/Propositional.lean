/-
Examples in propositional logic.
-/

-- From TPIL
import Auto.Tactic

section
variable (P Q R S : Prop)

example :P ∧ Q ↔ Q ∧ P := by auto
example :P ∨ Q ↔ Q ∨ P := by auto
example : (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) := by auto
example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) := by auto
example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by auto
example : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by auto
example : (P → (Q → R)) ↔ (P ∧ Q → R) := by auto
example : ((P ∨ Q) → R) ↔ (P → R) ∧ (Q → R) := by auto
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by auto
example : ¬P ∨ ¬Q → ¬(P ∧ Q) := by auto
example : ¬(P ∧ ¬P) := by auto
example : P ∧ ¬Q → ¬(P → Q) := by auto
example : ¬P → (P → Q) := by auto
example : (¬P ∨ Q) → (P → Q) := by auto
example : P ∨ False ↔ P := by auto
example : P ∧ False ↔ False := by auto
example : ¬(P ↔ ¬P) := by auto
example : (P → Q) → (¬Q → ¬P) := by auto

-- classical

example : (P → R ∨ S) → ((P → R) ∨ (P → S)) := by auto
example : ¬(P ∧ Q) → ¬P ∨ ¬Q := by auto
example : ¬(P → Q) → P ∧ ¬Q := by auto
example : (P → Q) → (¬P ∨ Q) := by auto
example : (¬Q → ¬P) → (P → Q) := by auto
example : P ∨ ¬P := by auto
example : (((P → Q) → P) → P) := by auto

end

-- some others

section
variable (A B C : Prop)

example (h : A) (h₁ : ¬ B) : ¬ (A → B) := by auto
example : ¬ (A ↔ ¬ A) := by auto
example (h : A ↔ B) (h₁ : A ∧ B → C) (h₂ : ¬ A ∧ ¬ B → C) : C := by auto
example (h : A ↔ B) (h₁ : (A ∧ ¬ B) ∨ (¬ A ∧ B)) : C := by auto
example (h : A → B) (h₁ : A) : B := by auto
example (h : A → B) (h₁ : B → C) : A → C := by auto
example (h : A → B ∨ C) (h₁ : B → D) (h₂ : C → D) : A → D := by auto

end

-- from an old tauto test file by Nathaniel Thomas

section
variable (A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Prop)

example (H1 : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄)
  (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) : B₄ := by auto
example (H1 : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄)
  (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₄) : B₃ := by auto
example (H1 : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄)
  (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n3 : ¬B₃) (n3 : ¬B₄) : B₂ := by auto
example (H1 : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄)
  (a1 : A₁) (a2 : A₂) (a3 : A₃) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄) : B₁ := by auto

example (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄)
  (a1 : A₁) (a2 : A₂) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄) : ¬A₃ := by auto
example (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄)
  (a1 : A₁) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄) : ¬A₂ := by auto
example (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄)
  (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄) : ¬A₁ := by auto

-- H last, all pos
example (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃)
  (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : B₄ := by auto
example (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₄)
  (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : B₃ := by auto
example (a1 : A₁) (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n3 : ¬B₃) (n3 : ¬B₄)
  (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : B₂ := by auto
example (a1 : A₁) (a2 : A₂) (a3 : A₃) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄)
  (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : B₁ := by auto

example (a1 : A₁) (a2 : A₂) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄)
  (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : ¬A₃ := by auto
example (a1 : A₁) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄)
  (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : ¬A₂ := by auto
example (a2 : A₂) (a3 : A₃) (n1 : ¬B₁) (n2 : ¬B₂) (n3 : ¬B₃) (n3 : ¬B₄)
  (H : A₁ → A₂ → A₃ → B₁ ∨ B₂ ∨ B₃ ∨ B₄) : ¬A₁ := by auto

-- H first, all neg
example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄)
  (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) : ¬B₄ := by auto
example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄)
  (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b4 : B₄) : ¬B₃ := by auto
example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄)
  (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b3 : B₃) (b4 : B₄) : ¬B₂ := by auto
example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄)
  (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b2 : B₂) (b3 : B₃) (b4 : B₄) : ¬B₁ := by auto

example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄)
  (n1 : ¬A₁) (n2 : ¬A₂) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄) : ¬¬A₃ := by auto
example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄)
  (n1 : ¬A₁) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄) : ¬¬A₂ := by auto
example (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄)
  (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄) : ¬¬A₁ := by auto

-- H last, all neg
example (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃)
  (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬B₄ := by auto
example (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b4 : B₄)
  (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬B₃ := by auto
example (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b3 : B₃) (b4 : B₄)
  (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬B₂ := by auto
example (n1 : ¬A₁) (n2 : ¬A₂) (n3 : ¬A₃) (b2 : B₂) (b3 : B₃) (b4 : B₄)
  (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬B₁ := by auto

example (n1 : ¬A₁) (n2 : ¬A₂) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄)
  (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬¬A₃ := by auto
example (n1 : ¬A₁) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄)
  (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬¬A₂ := by auto
example (n2 : ¬A₂) (n3 : ¬A₃) (b1 : B₁) (b2 : B₂) (b3 : B₃) (b4 : B₄)
  (H : ¬A₁ → ¬A₂ → ¬A₃ → ¬B₁ ∨ ¬B₂ ∨ ¬B₃ ∨ ¬B₄) : ¬¬A₁ := by auto

end

section club
variable (Scottish RedSocks WearKilt Married GoOutSunday : Prop)

theorem NoMember : (¬Scottish → RedSocks) → (WearKilt ∨ ¬RedSocks) → (Married → ¬GoOutSunday) →
                 (GoOutSunday ↔ Scottish) → (WearKilt → Scottish ∧ Married) →
                 (Scottish → WearKilt) → False := by auto
end club
