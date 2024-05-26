import Auto.Lib.IsomType
import Auto.Lib.StringExtra
import Auto.Lib.BoolExtra

namespace Auto.Embedding


structure GLift.{u, v} (α : Sort u) : Sort (max u (v + 1)) where
  /-- Lift a value into `GLift α` -/    up ::
  /-- Extract a value from `GLift α` -/ down : α

def GLift.down.inj (x y : GLift α) (H : GLift.down x = GLift.down y) : x = y :=
  show GLift.up (GLift.down x) = GLift.up (GLift.down y) by rw [H]

def notLift.{u} (p : GLift.{1, u} Prop) :=
  GLift.up (Not p.down)

def andLift.{u} (p q : GLift.{1, u} Prop) :=
  GLift.up (And p.down q.down)

def orLift.{u} (p q : GLift.{1, u} Prop) :=
  GLift.up (Or p.down q.down)

def iffLift.{u} (p q : GLift.{1, u} Prop) :=
  GLift.up (Iff p.down q.down)

noncomputable def ofPropLift.{u} (p : GLift.{1, u} Prop) :=
  GLift.up (Bool.ofProp p.down)

def notbLift.{u} (p : GLift.{1, u} Bool) :=
  GLift.up (not p.down)

def andbLift.{u} (p q : GLift.{1, u} Bool) :=
  GLift.up (p.down && q.down)

def orbLift.{u} (p q : GLift.{1, u} Bool) :=
  GLift.up (p.down || q.down)

def naddLift.{u} (m n : GLift.{1, u} Nat) :=
  GLift.up (Nat.add m.down n.down)

def nsubLift.{u} (m n : GLift.{1, u} Nat) :=
  GLift.up (Nat.sub m.down n.down)

def nmulLift.{u} (m n : GLift.{1, u} Nat) :=
  GLift.up (Nat.mul m.down n.down)

def ndivLift.{u} (m n : GLift.{1, u} Nat) :=
  GLift.up (Nat.div m.down n.down)

def nmodLift.{u} (m n : GLift.{1, u} Nat) :=
  GLift.up (Nat.mod m.down n.down)

def nleLift.{u} (m n : GLift.{1, u} Nat) :=
  GLift.up (Nat.le m.down n.down)

def nltLift.{u} (m n : GLift.{1, u} Nat) :=
  GLift.up (Nat.lt m.down n.down)

def nmaxLift.{u} (m n : GLift.{1, u} Nat) :=
  GLift.up (Nat.max m.down n.down)

def nminLift.{u} (m n : GLift.{1, u} Nat) :=
  GLift.up (Nat.min m.down n.down)

def iofNatLift.{u} (m : GLift.{1, u} Nat) :=
  GLift.up (Int.ofNat m.down)

def inegSuccLift.{u} (m : GLift.{1, u} Nat) :=
  GLift.up (Int.negSucc m.down)

def inegLift.{u} (m : GLift.{1, u} Int) :=
  GLift.up (Int.neg m.down)

def iabsLift.{u} (m : GLift.{1, u} Int) :=
  GLift.up (ite (m.down < -m.down) (-m.down) m.down)

def iaddLift.{u} (m n : GLift.{1, u} Int) :=
  GLift.up (Int.add m.down n.down)

def isubLift.{u} (m n : GLift.{1, u} Int) :=
  GLift.up (Int.sub m.down n.down)

def imulLift.{u} (m n : GLift.{1, u} Int) :=
  GLift.up (Int.mul m.down n.down)

def idivLift.{u} (m n : GLift.{1, u} Int) :=
  GLift.up (Int.div m.down n.down)

def imodLift.{u} (m n : GLift.{1, u} Int) :=
  GLift.up (Int.mod m.down n.down)

def iedivLift.{u} (m n : GLift.{1, u} Int) :=
  GLift.up (Int.ediv m.down n.down)

def iemodLift.{u} (m n : GLift.{1, u} Int) :=
  GLift.up (Int.emod m.down n.down)

def ileLift.{u} (m n : GLift.{1, u} Int) :=
  GLift.up (Int.le m.down n.down)

def iltLift.{u} (m n : GLift.{1, u} Int) :=
  GLift.up (Int.lt m.down n.down)

def imaxLift.{u} (m n : GLift.{1, u} Int) :=
  GLift.up (max m.down n.down)

def iminLift.{u} (m n : GLift.{1, u} Int) :=
  GLift.up (min m.down n.down)

def sappLift.{u} (m n : GLift.{1, u} String) :=
  GLift.up (String.append m.down n.down)

-- **TODO**
def slengthLift.{u} (m : GLift.{1, u} String) : GLift.{1, u} Nat :=
  GLift.up (String.length m.down)

def sleLift.{u} (m n : GLift.{1, u} String) : GLift.{1, u} Prop :=
  GLift.up (String.le m.down n.down)

def sltLift.{u} (m n : GLift.{1, u} String) : GLift.{1, u} Prop :=
  GLift.up (String.lt m.down n.down)

def sprefixofLift.{u} (m n : GLift.{1, u} String) : GLift.{1, u} Bool :=
  GLift.up (String.isPrefixOf m.down n.down)

def srepallLift.{u} (s patt rep: GLift.{1, u} String) : GLift.{1, u} String :=
  GLift.up (String.replace s.down patt.down rep.down)

def bvofNatLift.{u} (n : Nat) (x : GLift.{1, u} Nat) : GLift.{1, u} (BitVec n) :=
  GLift.up (BitVec.ofNat n x.down)

def bvtoNatLift.{u} (n : Nat) (x : GLift.{1, u} (BitVec n)) : GLift.{1, u} Nat :=
  GLift.up (BitVec.toNat x.down)

def bvofIntLift.{u} (n : Nat) (x : GLift.{1, u} Int) : GLift.{1, u} (BitVec n) :=
  GLift.up (BitVec.ofInt n x.down)

def bvtoIntLift.{u} (n : Nat) (x : GLift.{1, u} (BitVec n)) : GLift.{1, u} Int :=
  GLift.up (BitVec.toInt x.down)

def bvaddLift.{u} (n : Nat) (x y : GLift.{1, u} (BitVec n)) : GLift.{1, u} (BitVec n) :=
  GLift.up (BitVec.add x.down y.down)

def bvsubLift.{u} (n : Nat) (x y : GLift.{1, u} (BitVec n)) : GLift.{1, u} (BitVec n) :=
  GLift.up (BitVec.sub x.down y.down)

def bvnegLift.{u} (n : Nat) (x : GLift.{1, u} (BitVec n)) : GLift.{1, u} (BitVec n) :=
  GLift.up (BitVec.neg x.down)

def bvabsLift.{u} (n : Nat) (x : GLift.{1, u} (BitVec n)) : GLift.{1, u} (BitVec n) :=
  GLift.up (BitVec.abs x.down)

def bvmulLift.{u} (n : Nat) (x y : GLift.{1, u} (BitVec n)) : GLift.{1, u} (BitVec n) :=
  GLift.up (BitVec.mul x.down y.down)

def bvudivLift.{u} (n : Nat) (x y : GLift.{1, u} (BitVec n)) : GLift.{1, u} (BitVec n) :=
  GLift.up (BitVec.smtUDiv x.down y.down)

def bvuremLift.{u} (n : Nat) (x y : GLift.{1, u} (BitVec n)) : GLift.{1, u} (BitVec n) :=
  GLift.up (BitVec.umod x.down y.down)

def bvsdivLift.{u} (n : Nat) (x y : GLift.{1, u} (BitVec n)) : GLift.{1, u} (BitVec n) :=
  GLift.up (BitVec.smtSDiv x.down y.down)

def bvsremLift.{u} (n : Nat) (x y : GLift.{1, u} (BitVec n)) : GLift.{1, u} (BitVec n) :=
  GLift.up (BitVec.srem x.down y.down)

def bvsmodLift.{u} (n : Nat) (x y : GLift.{1, u} (BitVec n)) : GLift.{1, u} (BitVec n) :=
  GLift.up (BitVec.smod x.down y.down)

def bvmsbLift.{u} (n : Nat) (x : GLift.{1, u} (BitVec n)) : GLift.{1, u} Bool :=
  GLift.up (BitVec.msb x.down)

def bvultLift.{u} (n : Nat) (x y : GLift.{1, u} (BitVec n)) : GLift.{1, u} Bool :=
  GLift.up (BitVec.ult x.down y.down)

def bvuleLift.{u} (n : Nat) (x y : GLift.{1, u} (BitVec n)) : GLift.{1, u} Bool :=
  GLift.up (BitVec.ule x.down y.down)

def bvsltLift.{u} (n : Nat) (x y : GLift.{1, u} (BitVec n)) : GLift.{1, u} Bool :=
  GLift.up (BitVec.slt x.down y.down)

def bvsleLift.{u} (n : Nat) (x y : GLift.{1, u} (BitVec n)) : GLift.{1, u} Bool :=
  GLift.up (BitVec.sle x.down y.down)

def bvpropultLift.{u} (n : Nat) (x y : GLift.{1, u} (BitVec n)) : GLift.{1, u} Prop :=
  GLift.up (x.down.toFin < y.down.toFin)

def bvpropuleLift.{u} (n : Nat) (x y : GLift.{1, u} (BitVec n)) : GLift.{1, u} Prop :=
  GLift.up (x.down.toFin <= y.down.toFin)

def bvpropsltLift.{u} (n : Nat) (x y : GLift.{1, u} (BitVec n)) : GLift.{1, u} Prop :=
  GLift.up (x.down.toInt < y.down.toInt)

def bvpropsleLift.{u} (n : Nat) (x y : GLift.{1, u} (BitVec n)) : GLift.{1, u} Prop :=
  GLift.up (x.down.toInt <= y.down.toInt)

def bvandLift.{u} (n : Nat) (x y : GLift.{1, u} (BitVec n)) : GLift.{1, u} (BitVec n) :=
  GLift.up (BitVec.and x.down y.down)

def bvorLift.{u} (n : Nat) (x y : GLift.{1, u} (BitVec n)) : GLift.{1, u} (BitVec n) :=
  GLift.up (BitVec.or x.down y.down)

def bvxorLift.{u} (n : Nat) (x y : GLift.{1, u} (BitVec n)) : GLift.{1, u} (BitVec n) :=
  GLift.up (BitVec.xor x.down y.down)

def bvnotLift.{u} (n : Nat) (x : GLift.{1, u} (BitVec n)) : GLift.{1, u} (BitVec n) :=
  GLift.up (BitVec.not x.down)

def bvshlLift.{u} (n : Nat) (a : GLift.{1, u} (BitVec n)) (s : GLift.{1, u} Nat) : GLift.{1, u} (BitVec n) :=
  GLift.up (BitVec.shiftLeft a.down s.down)

def bvlshrLift.{u} (n : Nat) (a : GLift.{1, u} (BitVec n)) (s : GLift.{1, u} Nat) : GLift.{1, u} (BitVec n) :=
  GLift.up (BitVec.ushiftRight a.down s.down)

def bvashrLift.{u} (n : Nat) (a : GLift.{1, u} (BitVec n)) (s : GLift.{1, u} Nat) : GLift.{1, u} (BitVec n) :=
  GLift.up (BitVec.sshiftRight a.down s.down)

def bvsmtshlLift.{u} (n : Nat) (a : GLift.{1, u} (BitVec n)) (s : GLift.{1, u} (BitVec n)) : GLift.{1, u} (BitVec n) :=
  GLift.up (BitVec.shiftLeft a.down s.down.toNat)

def bvsmtlshrLift.{u} (n : Nat) (a : GLift.{1, u} (BitVec n)) (s : GLift.{1, u} (BitVec n)) : GLift.{1, u} (BitVec n) :=
  GLift.up (BitVec.ushiftRight a.down s.down.toNat)

def bvsmtashrLift.{u} (n : Nat) (a : GLift.{1, u} (BitVec n)) (s : GLift.{1, u} (BitVec n)) : GLift.{1, u} (BitVec n) :=
  GLift.up (BitVec.sshiftRight a.down s.down.toNat)

def bvappendLift.{u} (n m : Nat) (x : GLift.{1, u} (BitVec n)) (y : GLift.{1, u} (BitVec m)) : GLift.{1, u} (BitVec (Nat.add n m)) :=
  GLift.up (BitVec.append x.down y.down)

def bvextractLift.{u} (n h l : Nat) (x : GLift.{1, u} (BitVec n)) : GLift.{1, u} (BitVec (Nat.add (Nat.sub h l) 1)) :=
  GLift.up (BitVec.extractLsb h l x.down)

def bvrepeatLift.{u} (w i : Nat) (x : GLift.{1, u} (BitVec w)) : GLift.{1, u} (BitVec (Nat.mul w i)) :=
  GLift.up (BitVec.replicate i x.down)

def bvzeroExtendLift.{u} (w v : Nat) (x : GLift.{1, u} (BitVec w)) : GLift.{1, u} (BitVec v) :=
  GLift.up (BitVec.zeroExtend v x.down)

def bvsignExtendLift.{u} (w i : Nat) (x : GLift.{1, u} (BitVec w)) : GLift.{1, u} (BitVec i) :=
  GLift.up (BitVec.signExtend i x.down)

def constId {a : Sort u} {b : Sort v} (_ : a) (h : b) := h

@[reducible] def ImpF.{u, v} (p : Sort u) (q : Sort v) := p → q

def impLift.{u}
  (p : GLift.{t + 1, v} (Sort t))
  (q : GLift.{u + 1, v} (Sort u)) :=
  GLift.up (p.down → q.down)

def LiftTyConv.{u, v} (tyUp : GLift.{u + 1, v} (Sort u)) :=
  GLift.{u, v} (GLift.down.{u + 1, v} tyUp)

-- Isomorphic domain, β is the lifted one
def eqLift.{u, v, w} {α : Sort u} {β : Sort v} (I : IsomType α β) (x y : β) :=
  GLift.up.{_, w} (I.g x = I.g y)

def eqLift_refl.{u, v, w} {α : Sort u} {β : Sort v} (I : IsomType α β) (x : β) :
  GLift.down (eqLift.{u, v, w} I x x) := rfl

def eqLift.down.{u, v, w} {α : Sort u} {β : Sort v} (I : IsomType α β)
  (x y : β) (H : GLift.down (eqLift.{u, v, w} I x y)) : x = y :=
  let H₁ : I.f (I.g x) = I.f (I.g y) := H ▸ rfl
  let H₂ : x = I.f (I.g y) := I.eq₂ x ▸ H₁
  I.eq₂ y ▸ H₂

def eqLift.up.{u, v, w} {α : Sort u} {β : Sort v} (I : IsomType α β)
  (x y : β) (H : x = y) : GLift.down (eqLift.{u, v, w} I x y) :=
  H ▸ eqLift_refl.{u, v, w} I x

structure EqLift (β : Sort u) where
  eqF  : β → β → GLift.{1, v} Prop
  down : ∀ (x y : β), (eqF x y).down → x = y
  up   : ∀ (x y : β), x = y → (eqF x y).down

def EqLift.ofIsomTy {α : Sort u} {β : Sort v} (I : IsomType α β) : EqLift.{v, w} β :=
  ⟨eqLift.{u, v, w} I, eqLift.down.{u, v, w} I, eqLift.up.{u, v, w} I⟩

def eqLiftFn.{u} (β : Type u) (x y : β) := GLift.up.{1, u} (@Eq β x y)

def EqLift.default (β : Sort u) : EqLift β :=
  ⟨fun x y => GLift.up (@Eq β x y), fun _ _ => id, fun _ _ => id⟩

theorem eqGLift_equiv (a b : α) : (GLift.up a = GLift.up b) = (a = b) := by
  simp

theorem neGLift_equiv (a b : α) : (GLift.up a ≠ GLift.up b) = (a ≠ b) := by
  simp

@[reducible] def forallF {α : Sort u} (p : α → Sort v) := ∀ (x : α), p x

-- Isomorphic domain, β is the lifted one
def forallLift.{u, v, w, x} {α : Sort u} {β : Sort v} (I : IsomType α β)
  (p : β → GLift.{w + 1, x} (Sort w)) :=
  GLift.up.{(imax u w) + 1, x} (∀ (x : α), GLift.down (p (I.f x)))

def forallLift.down.{u, v, w, x}
  {α : Sort u} {β : Sort v} (I : IsomType α β)
  (p : β → GLift.{w + 1, x} (Sort w)) (H : GLift.down (forallLift I p))
  (x : β) : GLift.down (p x) :=
  I.eq₂ x ▸ H (I.g x)

def forallLift.up
  {α : Sort u} {β : Sort v} (I : IsomType α β)
  (p : β → GLift.{w + 1, x} (Sort w))
  (H : ∀ (x : β), GLift.down (p x)) : GLift.down (forallLift I p) :=
  fun x => I.eq₁ x ▸ H (I.f x)

structure ForallLift (β : Sort v') where
  forallF : (β → GLift.{w + 1, v} (Sort w)) → GLift.{w' + 1, v} (Sort w')
  down    : ∀ (p : β → GLift.{w + 1, v} (Sort w)), (forallF p).down → (∀ x : β, (p x).down)
  up      : ∀ (p : β → GLift.{w + 1, v} (Sort w)), (∀ x : β, (p x).down) → (forallF p).down

def ForallLift.ofIsomTy.{u, v, w, x} {α : Sort u} {β : Sort v} (I : IsomType α β) : ForallLift β :=
  ⟨forallLift.{u, v, w, x} I, forallLift.down I, forallLift.up I⟩

def forallLiftFn.{u} (β : Type u) (p : β → GLift.{1, u} Prop) := GLift.up.{1, u} (∀ x, GLift.down (p x))

def ForallLift.default (β : Sort v') : ForallLift.{v', v, w, imax v' w} β :=
  ⟨fun (p : β → GLift.{w + 1, v} (Sort w)) => GLift.up (∀ (x : β), GLift.down (p x)), fun _ => id, fun _ => id⟩

theorem forallGLift_equiv (p : β → Prop) : (∀ (x : GLift β), p x.down) = (∀ x, p x) := by
  apply propext (Iff.intro ?mp ?mpr) <;> intros h x <;> apply h

set_option pp.universes true
-- Isomorphic domain, β is the lifted one
def existLift {α : Sort u} {β : Sort v} (I : IsomType α β)
  (p : β → GLift.{1, x} Prop) :=
  GLift.up.{_, x} (∃ (x : α), GLift.down (p (I.f x)))

def existLift.down
  {α : Sort u} {β : Sort v} (I : IsomType α β)
  (p : β → GLift.{1, x} Prop)
  (H : GLift.down (existLift I p)) : ∃ x, GLift.down (p x) := by
  cases H; case intro x proof => exists I.f x;

def existLift.up
  {α : Sort u} {β : Sort v} (I : IsomType α β)
  (p : β → GLift.{1, x} Prop)
  (H : ∃ x, GLift.down (p x)) : GLift.down (existLift I p) := by
  cases H; case intro x proof => exists I.g x; rw [I.eq₂]; exact proof

structure ExistLift (β : Sort v') where
  existF  : (β → GLift.{1, v} Prop) → GLift.{1, v} Prop
  down    : ∀ (p : β → GLift.{1, v} Prop), (existF p).down → (∃ x : β, (p x).down)
  up      : ∀ (p : β → GLift.{1, v} Prop), (∃ x : β, (p x).down) → (existF p).down

def ExistLift.ofIsomTy.{u, v, x} {α : Sort u} {β : Sort v} (I : IsomType α β) : ExistLift β :=
  ⟨existLift.{u, v, x} I, existLift.down I, existLift.up I⟩

def existLiftFn.{u} (β : Type u) (p : β → GLift.{1, u} Prop) := GLift.up.{1, u} (∃ x, GLift.down (p x))

def ExistLift.default (β : Sort v') : ExistLift.{v', w} β :=
  ⟨fun (p : β → GLift.{1, w} Prop) => GLift.up (∃ (x : β), GLift.down (p x)), fun _ => id, fun _ => id⟩

theorem existGLift_equiv (p : β → Prop) : (∃ (x : GLift β), p x.down) = (∃ x, p x) := by
  apply propext (Iff.intro ?mp ?mpr) <;> intro ⟨x, h⟩
  case mp => exact ⟨x.down, h⟩
  case mpr => exact ⟨GLift.up x, h⟩

-- Isomorphic domain, β is the lifted one
noncomputable def iteLift {α : Sort u} {β : Sort v} (I : IsomType α β) (b : GLift.{_, x} Prop) (x y : β) :=
  I.f (Bool.ite' b.down (I.g x) (I.g y))

def iteLift.wf
  {α : Sort u} {β : Sort v} (I : IsomType α β)
  (p : GLift.{_, x} Prop) (x y : β) : iteLift I p x y = Bool.ite' p.down x y := by
  cases p; case up p =>
    cases Classical.em p <;> dsimp [iteLift]
    case inl hp => simp [Bool.ite'_eq_true _ _ _ hp, IsomType.eq₂ I]
    case inr hp => simp [Bool.ite'_eq_false _ _ _ hp, IsomType.eq₂ I]

structure IteLift (β : Sort v') where
  iteF : GLift.{1, v} Prop → β → β → β
  wf    : ∀ (b : GLift.{1, v} Prop) (x y : β), iteF b x y = Bool.ite' b.down x y

noncomputable def IteLift.ofIsomTy.{u, v, x} {α : Sort u} {β : Sort v} (I : IsomType α β) : IteLift.{v, x} β :=
  ⟨iteLift.{u, v, x} I, iteLift.wf I⟩

noncomputable def iteLiftFn.{u} (β : Type u) (b : GLift.{1, u} Prop) (x y : β) := Bool.ite' b.down x y

noncomputable def IteLift.default (β : Sort v') : IteLift.{v', w} β :=
  ⟨fun b x y => Bool.ite' b.down x y, fun _ _ _ => rfl⟩

-- !! First generalization (of `EqLift`)
--
-- structure FLift (β : Sort u) (f : ∀ (α : Sort u), α → α → Prop) where
--   fF   : β → β → Prop
--   down : ∀ (x y : β), fF x y → f β x y
--   up   : ∀ (x y : β), f β x y → fF x y
--
-- !! Rewrite of the above `FLift`
--
-- structure FLift (β : Sort u) (f : ∀ (α : Sort u), PProd α α → Prop) where
--   fF   : PProd β β → Prop
--   down : ∀ (x y : β), fF ⟨x, y⟩ → f β ⟨x, y⟩
--   up   : ∀ (x y : β), f β ⟨x, y⟩ → fF ⟨x, y⟩
--
-- !!Seite Generalization (of the above `FLift`)
--
-- structure FLift (β : Sort u) (γ : Sort u → Sort u) (f : ∀ (α : Sort u), γ α → Prop) where
--   fF   : γ β → Prop
--   down : ∀ (x : γ β), fF x → f β x
--   up   : ∀ (x : γ β), f β x → fF x

end Auto.Embedding
