module

public import Auto.Embedding.LamBase.BaseTerm

@[expose] public section

/-! Valuations `LamValuation` and the interpretation of base terms -/

namespace Auto.Embedding.Lam

structure ILLift (β : Type u) where
  eqL     : EqLift.{u + 1, u} β
  forallL : ForallLift.{u + 1, u, 0, 0} β
  existL  : ExistLift.{u + 1, u} β
  iteL    : IteLift.{u + 1, u} β

noncomputable def ILLift.ofIsomTy {α : Sort u} {β : Type v} (I : IsomType α β) : ILLift β :=
  ⟨EqLift.ofIsomTy I, ForallLift.ofIsomTy I, ExistLift.ofIsomTy I, IteLift.ofIsomTy I⟩

noncomputable def ILLift.default (β : Type u) : ILLift β :=
  ⟨EqLift.default β, ForallLift.default β, ExistLift.default β, IteLift.default β⟩

structure LamValuation extends LamTyVal where
  tyVal    : Nat → Type u
  varVal   : ∀ (n : Nat), (lamVarTy n).interp tyVal
  ilVal    : ∀ (n : Nat), ILLift.{u} ((lamILTy n).interp tyVal)
  eVarVal  : ∀ (n : Nat), (lamEVarTy n).interp tyVal

noncomputable def LamBaseTerm.interp (lval : LamValuation.{u}) : (b : LamBaseTerm) → (b.lamCheck lval.toLamTyVal).interp lval.tyVal
| .pcst pc    => pc.interp lval.tyVal
| .bcst bc    => bc.interp lval.tyVal
| .ncst nc    => nc.interp lval.tyVal
| .icst ic    => ic.interp lval.tyVal
| .scst sc    => sc.interp lval.tyVal
| .bvcst bvc  => bvc.interp lval.tyVal
| .ocst oc    => oc.interp lval.tyVal
| .eqI n      => (lval.ilVal n).eqL.eqF
| .forallEI n => (lval.ilVal n).forallL.forallF
| .existEI n  => (lval.ilVal n).existL.existF
| .iteI n     => (lval.ilVal n).iteL.iteF
| .eq s       => eqLiftFn (s.interp lval.tyVal)
| .forallE s  => forallLiftFn (s.interp lval.tyVal)
| .existE s   => existLiftFn (s.interp lval.tyVal)
| .ite s      => iteLiftFn (s.interp lval.tyVal)

noncomputable def LamBaseTerm.LamWF.interp (lval : LamValuation.{u}) : (lwf : LamWF lval.toLamTyVal b s) → s.interp lval.tyVal
| .ofPcst wf    => wf.interp lval.tyVal
| .ofBcst wf    => wf.interp lval.tyVal
| .ofNcst wf    => wf.interp lval.tyVal
| .ofIcst wf    => wf.interp lval.tyVal
| .ofScst wf    => wf.interp lval.tyVal
| .ofBvcst wf   => wf.interp lval.tyVal
| .ofOcst wf    => wf.interp lval.tyVal
| .ofEqI n      => (lval.ilVal n).eqL.eqF
| .ofForallEI n => (lval.ilVal n).forallL.forallF
| .ofExistEI n  => (lval.ilVal n).existL.existF
| .ofIteI n     => (lval.ilVal n).iteL.iteF
| .ofEq s       => @eqLiftFn (s.interp lval.tyVal)
| .ofForallE s  => @forallLiftFn (s.interp lval.tyVal)
| .ofExistE s   => @existLiftFn (s.interp lval.tyVal)
| .ofIte s      => iteLiftFn (s.interp lval.tyVal)

theorem LamBaseTerm.LamWF.interp_heq (lval : LamValuation.{u})
  (lwf₁ : LamWF lval.toLamTyVal b₁ s₁)
  (lwf₂ : LamWF lval.toLamTyVal b₂ s₂)
  (HBeq : b₁ = b₂) : HEq (LamWF.interp lval lwf₁) (LamWF.interp lval lwf₂) := by
  cases HBeq;
  cases LamWF.unique lwf₁ lwf₂
  case intro seq lweq =>
    cases seq; cases lweq; apply HEq.rfl

theorem LamBaseTerm.LamWF.interp_lvalIrrelevance
  (lval₁ lval₂ : LamValuation.{u})
  (lwf₁ : LamWF lval₁.toLamTyVal b₁ s₁)
  (lwf₂ : LamWF lval₂.toLamTyVal b₂ s₂)
  (HBeq : b₁ = b₂)
  (hTyVal : lval₁.tyVal = lval₂.tyVal)
  (hLamILTy : lval₁.lamILTy = lval₂.lamILTy)
  (hILVal : HEq lval₁.ilVal lval₂.ilVal) :
  HEq (LamWF.interp lval₁ lwf₁) (LamWF.interp lval₂ lwf₂) := by
  cases HBeq
  cases lval₁
  case mk toLamTyVal₁ tyVal₁ varVal₁ ilVal₁ eVarVal₁ =>
    cases toLamTyVal₁
    case mk lamVarTy₁ lamILTy₁ lamEVarTy₁ =>
      cases lval₂
      case mk toLamTyVal₂ tyVal₂ varVal₂ ilVal₂ eVarVal₂ =>
        cases toLamTyVal₂
        case mk lamVarTy₂ lamILTy₂ lamEVarTy₂ =>
          dsimp at varVal₁ ilVal₁ eVarVal₁ lwf₁ varVal₂ ilVal₂ eVarVal₂ lwf₂
          dsimp at hTyVal hLamILTy hILVal;
          cases hTyVal; cases hLamILTy; cases hILVal
          cases lwf₁ <;> cases lwf₂ <;> dsimp [interp] <;> try apply HEq.rfl
          case ofPcst => apply PropConst.LamWF.interp_lvalIrrelevance <;> rfl
          case ofBcst => apply BoolConst.LamWF.interp_lvalIrrelevance <;> rfl
          case ofNcst => apply NatConst.LamWF.interp_lvalIrrelevance <;> rfl
          case ofIcst => apply IntConst.LamWF.interp_lvalIrrelevance <;> rfl
          case ofScst => apply StringConst.LamWF.interp_lvalIrrelevance <;> rfl
          case ofBvcst => apply BitVecConst.LamWF.interp_lvalIrrelevance <;> rfl
          case ofOcst => apply OtherConst.LamWF.interp_lvalIrrelevance <;> rfl

theorem LamBaseTerm.interp_equiv (lval : LamValuation.{u})
  (lwf : LamWF lval.toLamTyVal b s) :
  HEq (LamWF.interp lval lwf) (interp lval b) := by
  cases lwf <;> try rfl
  case ofPcst => apply PropConst.interp_equiv
  case ofBcst => apply BoolConst.interp_equiv
  case ofNcst => apply NatConst.interp_equiv
  case ofIcst => apply IntConst.interp_equiv
  case ofScst => apply StringConst.interp_equiv
  case ofBvcst => apply BitVecConst.interp_equiv
  case ofOcst => apply OtherConst.interp_equiv

def LamValuation.insertEVarAt (lval : LamValuation.{u})
  (ty : LamSort) (val : ty.interp lval.tyVal) (pos : Nat) :=
  {lval with lamEVarTy := replaceAt ty pos lval.lamEVarTy,
             eVarVal := replaceAtDep val pos lval.eVarVal}

theorem LamTyVal.insertEVarAt_eVarIrrelevance
  {ltv₁ : LamTyVal} (H : n < pos) :
  let ltv₂ := {ltv₁ with lamEVarTy := replaceAt ty pos ltv₁.lamEVarTy}
  ltv₁.lamEVarTy n = ltv₂.lamEVarTy n := by
  dsimp [replaceAt]
  cases h : Nat.beq n pos
  case true =>
    dsimp; cases Nat.eq_of_beq_eq_true h;
    have H' := (Nat.not_le).mpr H; apply False.elim (H' _); apply Nat.le_refl
  case false => rfl

theorem LamValuation.insertEVarAt_eVarIrrelevance
  {lval₁ : LamValuation.{u}} {val} (H : n < pos) :
  let lval₂ := lval₁.insertEVarAt ty val pos;
  lval₁.lamEVarTy n = lval₂.lamEVarTy n ∧ HEq (lval₁.eVarVal n) (lval₂.eVarVal n) := by
  dsimp [insertEVarAt, replaceAt, replaceAtDep]
  cases h : Nat.beq n pos
  case true =>
    dsimp; cases Nat.eq_of_beq_eq_true h;
    have H' := (Nat.not_le).mpr H; apply False.elim (H' _); apply Nat.le_refl
  case false => apply And.intro rfl HEq.rfl

end Auto.Embedding.Lam
