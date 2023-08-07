import Auto.Util.SigEq
namespace Auto.Embedding

@[reducible] def pushLCtx (lctx : Nat → α) (x : α) : Nat → α
| 0     => x
| n + 1 => lctx n

def pushLCtx.comm (f : α → β) (lctx : Nat → α) (x : α) :
  (n : Nat) → f (pushLCtx lctx x n) = pushLCtx (fun n => f (lctx n)) (f x) n
| 0       => rfl
| .succ _ => rfl

theorem pushLCtx.commFn (f : α → β) (lctx : Nat → α) (x : α) :
  (fun n => f (pushLCtx lctx x n)) = (fun n => pushLCtx (fun n => f (lctx n)) (f x) n) :=
  funext (pushLCtx.comm f lctx x)

@[reducible] def pushLCtxDep {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) : ∀ n, lctxty (pushLCtx rty xty n)
| 0     => x
| n + 1 => lctx n

def pushLCtxDep.comm {α : Sort w} {β : α → Sort x} {rty : Nat → α} {lctxty : α → Sort u}
  (f : ∀ (x : α), lctxty x → β x) (lctx : ∀ n, lctxty (rty n))
  {xty : α} (x : lctxty xty) : (n : Nat) →
  f _ (pushLCtxDep lctx x n) = pushLCtxDep (lctxty:=β) (fun n => f _ (lctx n)) (f xty x) n
| 0 => rfl
| _ + 1  => rfl

def pushLCtxDep.absorbAux {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) :
  (n : Nat) → HEq
    (@pushLCtxDep _ rty lctxty lctx _ x n)
    (@pushLCtxDep _ (lctxty ∘ rty) id lctx _ x n)
| 0 => HEq.refl _
| _ + 1 => HEq.refl _

theorem pushLCtxDep.absorb {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) :
  PSigmaEq (fun (α : Nat → Sort u) => (∀ (n : Nat), α n))
    (@pushLCtxDep _ rty lctxty lctx _ x) (@pushLCtxDep _ (lctxty ∘ rty) id lctx _ x) :=
  PSigmaEq.of_heq _ (HEq.funext _ _ (pushLCtxDep.absorbAux _ _)) (pushLCtx.commFn _ _ _)

def pushLCtxAt (lctx : Nat → α) (x : α) (pos n : Nat) : α :=
  match n.ble pos with
  | true => 
    match n.beq pos with
    | true => x
    | false => lctx n
  | false => lctx (.pred n)

def pushLCtxAtRec (lctx : Nat → α) (x : α) : (pos : Nat) → Nat → α
| 0 => pushLCtx lctx x
| pos' + 1 => fun n =>
  match n with
  | 0 => lctx 0
  | n' + 1 => pushLCtxAtRec (fun n => lctx (Nat.succ n)) x pos' n'

theorem pushLCtxAt.equiv (lctx : Nat → α) (x : α) (pos n : Nat) :
  pushLCtxAtRec lctx x pos n = pushLCtxAt lctx x pos n := by
  revert lctx n; induction pos <;> intro lctx n
  case zero =>
    cases n <;> rfl
  case succ pos' IH =>
    cases n
    case zero => rfl
    case succ n' =>
      let IH' := IH (fun n => lctx (.succ n)) n'
      dsimp [pushLCtxAtRec, pushLCtxAt, Nat.ble, Nat.beq]
      dsimp [pushLCtxAtRec, pushLCtxAt, Nat.ble, Nat.beq] at IH'
      cases n'
      case zero =>
        rw [Nat.ble_eq_true_of_le (Nat.zero_le _)]; dsimp
        rw [Nat.ble_eq_true_of_le (Nat.zero_le _)] at IH'; dsimp at IH'
        exact IH'
      case succ n' =>
        exact IH'

def pushLCtxAtRec.comm (f : α → β) (lctx : Nat → α) (x : α) :
  (pos : Nat) → (n : Nat) → f (pushLCtxAtRec lctx x pos n) = pushLCtxAtRec (f ∘ lctx) (f x) pos n
| 0 => fun n => by
  dsimp [pushLCtxAtRec]; apply pushLCtx.comm
| pos' + 1 => fun n =>
  match n with
  | 0 => rfl
  | n' + 1 => pushLCtxAtRec.comm f (fun n => lctx (Nat.succ n)) x pos' n'

theorem pushLCtxAtRec.commFn (lctx : Nat → α) (f : α → β) (x : α) (pos : Nat) :
  (fun n => f (pushLCtxAtRec lctx x pos n)) = (fun n => pushLCtxAtRec (fun n => f (lctx n)) (f x) pos n) :=
  funext (pushLCtxAtRec.comm f lctx x pos)

-- Surprisingly, this is definitionally equal
def pushLCtx_pushLCtxAtRec (lctx : Nat → α) (x y : α) (pos : Nat) :
  pushLCtx (pushLCtxAtRec lctx x pos) y = pushLCtxAtRec (pushLCtx lctx y) x (Nat.succ pos)
  := rfl

def pushLCtxAtDep {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) (pos n : Nat) : lctxty (pushLCtxAt rty xty pos n) := by
  dsimp [pushLCtxAt]
  match n.ble pos with
  | true =>
    match n.beq pos with
    | true => exact x
    | false => exact (lctx n)
  | false => exact (lctx (.pred n))

def pushLCtxAtDepRec {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) : (pos : Nat) → (n : Nat) → lctxty (pushLCtxAtRec rty xty pos n)
| 0 => pushLCtxDep lctx x
| pos' + 1 => fun n =>
  match n with
  | 0 => lctx 0
  | n' + 1 => pushLCtxAtDepRec (fun n => lctx (Nat.succ n)) x pos' n'

def pushLCtxAtDep.equiv {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) (pos n : Nat) :
  HEq (pushLCtxAtDepRec lctx x pos n) (pushLCtxAtDep lctx x pos n) := by
  dsimp [pushLCtxAtDep, pushLCtxAt];
  revert rty lctx n; induction pos <;> intro rty lctx n
  case zero =>
    cases n <;> apply HEq.refl
  case succ pos' IH =>
    cases n
    case zero => apply HEq.rfl
    case succ n' =>
      let IH' := IH (fun n => lctx (.succ n)) n'
      dsimp [pushLCtxAtDepRec, pushLCtxAtRec, Nat.ble, Nat.beq]
      dsimp [pushLCtxAtDepRec, pushLCtxAtRec, Nat.ble, Nat.beq] at IH'
      cases n'
      case zero =>
        rw [Nat.ble_eq_true_of_le (Nat.zero_le _)]; dsimp
        rw [Nat.ble_eq_true_of_le (Nat.zero_le _)] at IH'; dsimp at IH'
        exact IH'
      case succ n' =>
        exact IH'

def pushLCtxAtDepRec.comm {α : Sort w} {β : α → Sort x} {rty : Nat → α} {lctxty : α → Sort u}
  (f : ∀ (x : α), lctxty x → β x) (lctx : ∀ n, lctxty (rty n))
  {xty : α} (x : lctxty xty) : (pos : Nat) → (n : Nat) →
    f _ (pushLCtxAtDepRec lctx x pos n) = pushLCtxAtDepRec (lctxty:=β) (fun n => f _ (lctx n)) (f xty x) pos n
| 0 => fun _ => pushLCtxDep.comm _ _ _ _
| pos' + 1 => fun n =>
  match n with
  | 0 => rfl
  | n' + 1 => pushLCtxAtDepRec.comm f (fun n => lctx (Nat.succ n)) x pos' n'

def pushLCtxAtDepRec.nonDep {rty : Nat → α} {lctxty : Sort u}
  (lctx : Nat → lctxty) {xty : α} (x : lctxty) : (pos n : Nat) →
  @pushLCtxAtDepRec _ rty (fun _ => lctxty) lctx xty x pos n = pushLCtxAtRec lctx x pos n
| 0 => fun _ => rfl
| .succ pos' => fun n =>
  match n with
  | 0 => rfl
  | .succ n' => pushLCtxAtDepRec.nonDep (fun n => lctx (.succ n)) x pos' n'

def pushLCtxAtDepRec.absorbAux {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) :
  (pos : Nat) → (n : Nat) → HEq
    (@pushLCtxAtDepRec _ rty lctxty lctx _ x pos n)
    (@pushLCtxAtDepRec _ (lctxty ∘ rty) id lctx _ x pos n)
| 0 => fun _ => pushLCtxDep.absorbAux _ _ _
| pos' + 1 => fun n =>
  match n with
  | 0 => HEq.refl _
  | n' + 1 => pushLCtxAtDepRec.absorbAux (fun n => lctx (.succ n)) x pos' n'

theorem pushLCtxAtDepRec.absorb {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) (pos : Nat) :
  PSigmaEq (fun (α : Nat → Sort u) => (∀ (n : Nat), α n))
    (@pushLCtxAtDepRec _ rty lctxty lctx _ x pos) (@pushLCtxAtDepRec _ (lctxty ∘ rty) id lctx _ x pos) :=
  PSigmaEq.of_heq _ (HEq.funext _ _ (pushLCtxAtDepRec.absorbAux _ _ _)) (pushLCtxAtRec.commFn _ _ _ _)

-- Surprisingly, this is definitionally equal
def pushLCtxDep_pushLCtxAtDepRec {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) {yty : α} (y : lctxty yty) (pos : Nat) :
  pushLCtxDep (pushLCtxAtDepRec lctx x pos) y = pushLCtxAtDepRec (pushLCtxDep lctx y) x (Nat.succ pos) := rfl

def popLCtx (lctx : Nat → α) := fun n => lctx (n + 1)

def popLCtx.comm (f : α → β) (lctx : Nat → α) :
  (n : Nat) → f (popLCtx lctx n) = popLCtx (f ∘ lctx) n := fun _ => rfl

def popLCtx.commFn (f : α → β) (lctx : Nat → α) :
  (fun n => f (popLCtx lctx n)) = (fun n => popLCtx (f ∘ lctx) n) := rfl

def popLCtxDep {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) : ∀ n, lctxty (popLCtx rty n) :=
  fun n => lctx (n + 1)

def popLCtxDep.comm {α : Sort w} {β : α → Sort x} {rty : Nat → α} {lctxty : α → Sort u}
  (f : ∀ (x : α), lctxty x → β x) (lctx : ∀ n, lctxty (rty n)) (n : Nat) :
  f _ (popLCtxDep lctx n) = popLCtxDep (lctxty:=β) (fun n => f _ (lctx n)) n := rfl

def popLCtxDep.absorbAux {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) (n : Nat) : HEq
    (@popLCtxDep _ rty lctxty lctx n)
    (@popLCtxDep _ (lctxty ∘ rty) id lctx n) := HEq.refl _

theorem popLCtxDep.absorb {rty : Nat → α} {lctxty : α → Sort u} (lctx : ∀ n, lctxty (rty n)) :
  PSigmaEq (fun (α : Nat → Sort u) => (∀ (n : Nat), α n))
    (@popLCtxDep _ rty lctxty lctx) (@popLCtxDep _ (lctxty ∘ rty) id lctx) :=
  PSigmaEq.of_heq _ (HEq.funext _ _ (popLCtxDep.absorbAux _)) (popLCtx.commFn _ _)

def popLCtxAt (lctx : Nat → α) (pos n : Nat) :=
  match pos.ble n with
  | true => lctx (.succ n)
  | false => lctx n

def popLCtxAtRec (lctx : Nat → α) (pos : Nat) := 
  match pos with
  | 0 => popLCtx lctx
  | pos' + 1 => fun n =>
    match n with
    | 0 => lctx 0
    | n' + 1 => popLCtxAtRec (fun n => lctx (Nat.succ n)) pos' n'

theorem popLCtxAt.equiv (lctx : Nat → α) (pos n : Nat) :
  popLCtxAtRec lctx pos n = popLCtxAt lctx pos n := by
  revert lctx n; induction pos <;> intro lctx n
  case zero =>
    cases n <;> rfl
  case succ pos' IH =>
    cases n
    case zero => rfl
    case succ n' => exact (IH (fun n => lctx (.succ n)) n')

def popLCtxAtRec.comm (lctx : Nat → α) (f : α → β) (pos : Nat) :
  (n : Nat) → f (popLCtxAtRec lctx pos n) = popLCtxAtRec (f ∘ lctx) pos n :=
  match pos with
  | 0 => fun _ => rfl
  | pos' + 1 => fun n =>
    match n with
    | 0 => rfl
    | n' + 1 => popLCtxAtRec.comm (fun n => lctx (.succ n)) f pos' n'

def popLCtxAtRec.commFn (lctx : Nat → α) (f : α → β) (pos : Nat) :
  (fun n => f (popLCtxAtRec lctx pos n)) = (fun n => popLCtxAtRec (f ∘ lctx) pos n) :=
  funext (popLCtxAtRec.comm lctx f pos)

def popLCtxAtDep {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) (pos : Nat) (n : Nat) : lctxty (popLCtxAt rty pos n) := by
  dsimp [popLCtxAt]
  match pos.ble n with
  | true => exact lctx (.succ n)
  | false => exact lctx n

def popLCtxAtDepRec {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) : (pos : Nat) → (n : Nat) → lctxty (popLCtxAtRec rty pos n)
| 0 => popLCtxDep lctx
| pos' + 1 => fun n =>
  match n with
  | 0 => lctx 0
  | n' + 1 => popLCtxAtDepRec (fun n => lctx (Nat.succ n)) pos' n'

def popLCtxAtDepRec.absorbAux {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) : (pos : Nat) → (n : Nat) → HEq
    (@popLCtxAtDepRec _ rty lctxty lctx pos n)
    (@popLCtxAtDepRec _ (lctxty ∘ rty) id lctx pos n)
| 0 => fun _ => HEq.refl _
| pos' + 1 => fun n =>
  match n with
  | 0 => HEq.refl _
  | n' + 1 => popLCtxAtDepRec.absorbAux (fun n => lctx (.succ n)) pos' n'

def popLCtxAtDepRec.absorbAux' {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) (pos : Nat) (n : Nat) : HEq
    (@popLCtxAtDepRec _ rty lctxty lctx pos n)
    (@popLCtxAtDepRec _ id (lctxty ∘ rty) lctx pos n) :=
  HEq.trans
    (b := @popLCtxAtDepRec _ (lctxty ∘ rty) id lctx pos n)
    (popLCtxAtDepRec.absorbAux lctx pos n)
    (HEq.symm (@popLCtxAtDepRec.absorbAux _ id (lctxty ∘ rty) lctx pos n))

def popLCtxAtDepRec.absorb {rty : Nat → α} {lctxty : α → Sort u} (lctx : ∀ n, lctxty (rty n)) (pos : Nat):
  PSigmaEq (fun (α : Nat → Sort u) => (∀ (n : Nat), α n))
    (@popLCtxAtDepRec _ rty lctxty lctx pos) (@popLCtxAtDepRec _ (lctxty ∘ rty) id lctx pos) :=
  PSigmaEq.of_heq _ (HEq.funext _ _ (popLCtxAtDepRec.absorbAux _ _)) (popLCtxAtRec.commFn _ _ _)

def popLCtxAtDepRec.comm {α : Sort w} {β : α → Sort x} {rty : Nat → α} {lctxty : α → Sort u}
  (f : ∀ (x : α), lctxty x → β x) (lctx : ∀ n, lctxty (rty n)) :
  (pos : Nat) → (n : Nat) → f _ (popLCtxAtDepRec lctx pos n) = popLCtxAtDepRec (lctxty:=β) (fun n => f _ (lctx n)) pos n
| 0 => fun _ => rfl
| pos' + 1 => fun n =>
  match n with
  | 0 => rfl
  | n' + 1 => popLCtxAtDepRec.comm f (fun n => lctx (Nat.succ n)) pos' n'

def popLCtxAtRec.commDep
  {β : α → Sort u} (lctx : Nat → α) (f : ∀ (x : α), β x) :
  (pos n : Nat) → f (popLCtxAtRec lctx pos n) = popLCtxAtDepRec (fun n => f (lctx n)) pos n
| 0 => fun _ => rfl
| pos' + 1 => fun n =>
  match n with
  | 0 => rfl
  | n' + 1 => popLCtxAtRec.commDep (fun n => lctx (.succ n)) f pos' n'
 
-- #reduce fun lctx => popLCtxAtRec lctx 3 4

def push_pop_eq (lctx : Nat → α) :
  pushLCtx (popLCtx lctx) (lctx 0) = lctx := by
  apply funext
  intro n; cases n <;> rfl

def popAtRec_pushAtRec_eq (lctx : Nat → α) (x : α) :
  (pos : Nat) → (n : Nat) → popLCtxAtRec (pushLCtxAtRec lctx x pos) pos n = lctx n
| 0 => fun _ => rfl
| pos' + 1 => fun n =>
  match n with
  | 0 => rfl
  | n' + 1 => popAtRec_pushAtRec_eq (fun n => lctx (Nat.succ n)) x pos' n'

def popAtDepRec_pushAtDepRec_eq
  {α : Sort w} {rty : Nat → α} {lctxty : α → Sort u}
  (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) : (pos n : Nat) →
  HEq (@popLCtxAtDepRec _ (pushLCtxAtRec rty xty pos) lctxty
        (@pushLCtxAtDepRec _ rty lctxty lctx xty x pos) pos n
      )
      (lctx n)
| 0 => fun _ => HEq.rfl
| pos' + 1 => fun n =>
  match n with
  | 0 => HEq.rfl
  | n' + 1 => @popAtDepRec_pushAtDepRec_eq _ _ lctxty (fun n => lctx (Nat.succ n)) _ x pos' n'

def popLCtxsAt (lctx : Nat → α) (lvl pos n : Nat) :=
  match pos.ble n with
  | true => lctx (Nat.add n lvl)
  | false => lctx n

def popLCtxsAt.comm (f : α → β) (lctx : Nat → α) (lvl : Nat) (pos n : Nat) :
  f (popLCtxsAt lctx lvl pos n) = popLCtxsAt (f ∘ lctx) lvl pos n := by
  dsimp [popLCtxsAt]
  match Nat.ble pos n with
  | true => rfl
  | false => rfl

def popLCtxsAt.succ_l (lctx : Nat → α) (lvl : Nat) (pos n : Nat) :
  popLCtxsAt lctx (.succ lvl) pos n = popLCtxsAt (popLCtxAt lctx pos) lvl pos n := by
  dsimp [popLCtxsAt, popLCtxAt]
  match h : Nat.ble pos n with
  | true =>
    dsimp
    have leAdd' := Nat.le_trans (Nat.le_of_ble_eq_true h) (Nat.le_add_right _ lvl)
    have bleAdd' := Nat.ble_eq_true_of_le leAdd'
    rw [bleAdd']; rfl
  | false => rfl

def popLCtxsAt.one (lctx : Nat → α) :
  popLCtxsAt lctx 1 = popLCtxAt lctx := rfl

end Auto.Embedding