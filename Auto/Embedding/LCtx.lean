import Auto.Util.HEqExtra
import Std.Data.Nat.Lemmas
namespace Auto.Embedding

section push
  
  def pushLCtxAt (x : α) (pos : Nat) (lctx : Nat → α) (n : Nat) : α :=
    match n.ble pos with
    | true => 
      match n.beq pos with
      | true => x
      | false => lctx n
    | false => lctx (.pred n)
  
  theorem pushLCtxAt.succ_zero (x : α) (pos : Nat) (lctx : Nat → α) :
    pushLCtxAt x (.succ pos) lctx 0 = lctx 0 := rfl
  
  theorem pushLCtxAt.succ_succ (x : α) (pos : Nat) (lctx : Nat → α) (n : Nat) :
    pushLCtxAt x (.succ pos) lctx (.succ n) = pushLCtxAt x pos (fun n => lctx (.succ n)) n := by
    dsimp [pushLCtxAt, Nat.ble, Nat.beq];
    match h : Nat.ble n pos with
    | true => rfl
    | false =>
      dsimp; cases n;
      case zero =>
        have h' : Nat.ble Nat.zero pos = true :=
          Nat.ble_eq_true_of_le (Nat.zero_le _)
        rw [h] at h'; cases h'
      case succ n' => rfl
  
  theorem pushLCtxAt.succ_succ_Fn (x : α) (pos : Nat) (lctx : Nat → α) :
    (fun n => pushLCtxAt x (.succ pos) lctx (.succ n)) = pushLCtxAt x pos (fun n => lctx (.succ n)) :=
    funext (fun n => pushLCtxAt.succ_succ x pos lctx n)
  
  def pushLCtxAt.comm (f : α → β) (x : α) (pos : Nat) (lctx : Nat → α) (n : Nat) :
    f (pushLCtxAt x pos lctx n) = pushLCtxAt (f x) pos (f ∘ lctx) n := by
    dsimp [pushLCtxAt]
    match n.ble pos with
    | true =>
      match n.beq pos with
      | true => rfl
      | false => rfl
    | false => rfl
  
  theorem pushLCtxAt.commFn (f : α → β) (x : α) (pos : Nat) (lctx : Nat → α) :
    (fun n => f (pushLCtxAt x pos lctx n)) = (fun n => pushLCtxAt (f x) pos (fun n => f (lctx n)) n) :=
    funext (pushLCtxAt.comm f x pos lctx)
  
  def pushLCtxAtDep
    {rty : Nat → α} {lctxty : α → Sort u} {xty : α} (x : lctxty xty) (pos : Nat)
    (lctx : ∀ n, lctxty (rty n)) (n : Nat) : lctxty (pushLCtxAt xty pos rty n) := by
    dsimp [pushLCtxAt]
    match n.ble pos with
    | true =>
      match n.beq pos with
      | true => exact x
      | false => exact (lctx n)
    | false => exact (lctx (.pred n))
  
  theorem pushLCtxAtDep.succ_zero {rty : Nat → α} {lctxty : α → Sort u}
    {xty : α} (x : lctxty xty) (pos : Nat) (lctx : ∀ n, lctxty (rty n)) :
    pushLCtxAtDep x (.succ pos) lctx 0 = lctx 0 := rfl
  
  theorem pushLCtxAtDep.succ_succ {rty : Nat → α} {lctxty : α → Sort u} {xty : α}
    (x : lctxty xty) (pos : Nat) (lctx : ∀ n, lctxty (rty n)) (n : Nat) :
    HEq (pushLCtxAtDep x (.succ pos) lctx (.succ n)) (pushLCtxAtDep x pos (fun n => lctx (.succ n)) n) := by
    dsimp [pushLCtxAt, pushLCtxAtDep, Nat.ble, Nat.beq]
    match h : Nat.ble n pos with
    | true => rfl
    | false =>
      dsimp; cases n;
      case zero =>
        have h' : Nat.ble Nat.zero pos = true :=
          Nat.ble_eq_true_of_le (Nat.zero_le _)
        rw [h] at h'; cases h'
      case succ n' => rfl
  
  theorem pushLCtxAtDep.succ_succ_Fn {rty : Nat → α} {lctxty : α → Sort u}
    {xty : α} (x : lctxty xty) (pos : Nat) (lctx : ∀ n, lctxty (rty n)) :
    HEq (fun n => pushLCtxAtDep x (.succ pos) lctx (.succ n)) (pushLCtxAtDep x pos (fun n => lctx (.succ n))) :=
    HEq.funext _ _ (fun n => pushLCtxAtDep.succ_succ x pos lctx n)
  
  def pushLCtxAtDep.comm {α : Sort w} {β : α → Sort x} {rty : Nat → α} {lctxty : α → Sort u}
    (f : ∀ (x : α), lctxty x → β x) {xty : α} (x : lctxty xty) (pos : Nat)
    (lctx : ∀ n, lctxty (rty n)) (n : Nat) :
      f _ (pushLCtxAtDep x pos lctx n) = pushLCtxAtDep (lctxty:=β) (f xty x) pos (fun n => f _ (lctx n)) n := by
    dsimp [pushLCtxAt, pushLCtxAtDep]
    match n.ble pos with
    | true =>
      match n.beq pos with
      | true => rfl
      | false => rfl
    | false => rfl
  
  def pushLCtxAtDep.nonDep {rty : Nat → α} {lctxty : Sort u}
    {xty : α} (x : lctxty) (pos : Nat) (lctx : Nat → lctxty) (n : Nat) :
    @pushLCtxAtDep _ rty (fun _ => lctxty) xty x pos lctx n = pushLCtxAt x pos lctx n := rfl
  
  def pushLCtxAtDep.absorbAux {rty : Nat → α} {lctxty : α → Sort u}
    {xty : α} (x : lctxty xty) (pos : Nat) (lctx : ∀ n, lctxty (rty n)) (n : Nat) :
    HEq
      (@pushLCtxAtDep _ rty lctxty _ x pos lctx n)
      (@pushLCtxAtDep _ (lctxty ∘ rty) id _ x pos lctx n) := by
    dsimp [pushLCtxAt, pushLCtxAtDep]
    match n.ble pos with
    | true =>
      match n.beq pos with
      | true => apply HEq.rfl
      | false => apply HEq.rfl
    | false => apply HEq.rfl
  
  theorem pushLCtxAtDep.absorb {rty : Nat → α} {lctxty : α → Sort u}
    {xty : α} (x : lctxty xty) (pos : Nat) (lctx : ∀ n, lctxty (rty n)) :
    HEq (@pushLCtxAtDep _ rty lctxty _ x pos lctx) (@pushLCtxAtDep _ (lctxty ∘ rty) id _ x pos lctx) :=
    HEq.funext _ _ (pushLCtxAtDep.absorbAux _ _ _)
  
  @[reducible] def pushLCtx (x : α) (lctx : Nat → α) := pushLCtxAt x 0 lctx
  
  def pushLCtx.zero (x : α) (lctx : Nat → α) : pushLCtx x lctx 0 = x := rfl
  
  def pushLCtx.succ (x : α) (lctx : Nat → α) (n : Nat) : pushLCtx x lctx (.succ n) = lctx n := rfl
  
  def pushLCtx.succ_Fn (x : α) (lctx : Nat → α) :
    (fun n => pushLCtx x lctx (.succ n)) = lctx := rfl

  theorem pushLCtxAt.zero (x : α) (lctx : Nat → α) (n : Nat) :
    pushLCtxAt x 0 lctx n = pushLCtx x lctx n := rfl
  
  def pushLCtx.comm (f : α → β) (x : α) (lctx : Nat → α) (n : Nat) :
    f (pushLCtx x lctx n) = pushLCtx (f x) (fun n => f (lctx n)) n :=
    pushLCtxAt.comm f x 0 lctx n
  
  theorem pushLCtx.commFn (f : α → β) (x : α) (lctx : Nat → α) :
    (fun n => f (pushLCtx x lctx n)) = (fun n => pushLCtx (f x) (fun n => f (lctx n)) n) :=
    funext (pushLCtx.comm f x lctx)
  
  def pushLCtx_pushLCtxAt (x y : α) (pos : Nat) (lctx : Nat → α) :
    pushLCtx y (pushLCtxAt x pos lctx) = pushLCtxAt x (Nat.succ pos) (pushLCtx y lctx) := by
    apply funext; intro n; cases n; rfl; rw [pushLCtxAt.succ_succ]; rfl
  
  @[reducible] def pushLCtxDep {rty : Nat → α} {lctxty : α → Sort u}
    {xty : α} (x : lctxty xty) (lctx : ∀ n, lctxty (rty n)) := pushLCtxAtDep x 0 lctx
  
  def pushLCtxDep.zero {rty : Nat → α} {lctxty : α → Sort u}
    {xty : α} (x : lctxty xty) (lctx : ∀ n, lctxty (rty n)) :
    pushLCtxDep x lctx 0 = x := rfl
  
  def pushLCtxDep.succ {rty : Nat → α} {lctxty : α → Sort u}
    (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) (n : Nat) :
    pushLCtxDep x lctx (.succ n) = lctx n := rfl

  def pushLCtxDep.succ_Fn {rty : Nat → α} {lctxty : α → Sort u}
    (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) :
    (fun n => pushLCtxDep x lctx (.succ n)) = lctx := rfl
  
  theorem pushLCtxAtDep.zero {rty : Nat → α} {lctxty : α → Sort u}
    (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) (n : Nat) :
    pushLCtxAtDep x 0 lctx n = pushLCtxDep x lctx n := rfl
  
  def pushLCtxDep.comm {α : Sort w} {β : α → Sort x} {rty : Nat → α} {lctxty : α → Sort u}
    (f : ∀ (x : α), lctxty x → β x) (lctx : ∀ n, lctxty (rty n))
    {xty : α} (x : lctxty xty) (n : Nat) :
    f _ (pushLCtxDep x lctx n) = pushLCtxDep (lctxty:=β) (f xty x) (fun n => f _ (lctx n)) n :=
    pushLCtxAtDep.comm f x 0 lctx n
  
  def pushLCtxDep.absorbAux {rty : Nat → α} {lctxty : α → Sort u}
    (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) (n : Nat) :
    HEq
      (@pushLCtxDep _ rty lctxty _ x lctx n)
      (@pushLCtxDep _ (lctxty ∘ rty) id _ x lctx n) :=
    pushLCtxAtDep.absorbAux x 0 lctx n
  
  theorem pushLCtxDep.absorb {rty : Nat → α} {lctxty : α → Sort u}
    (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) :
    HEq (@pushLCtxDep _ rty lctxty _ x lctx) (@pushLCtxDep _ (lctxty ∘ rty) id _ x lctx) :=
    pushLCtxAtDep.absorb x 0 lctx
  
  -- Surprisingly, this is definitionally equal
  def pushLCtxDep_pushLCtxAtDep {rty : Nat → α} {lctxty : α → Sort u}
    (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) {yty : α} (y : lctxty yty) (pos : Nat) :
    HEq (pushLCtxDep y (pushLCtxAtDep x pos lctx)) (pushLCtxAtDep x (Nat.succ pos) (pushLCtxDep y lctx)) := by
    apply HEq.funext; intro n; cases n; rfl;
    apply HEq.trans _ (HEq.symm (pushLCtxAtDep.succ_succ _ _ _ _)); apply HEq.rfl
  
  @[reducible] def pushLCtxs (xs : List α) (lctx : Nat → α) (n : Nat) : α :=
    match h : Nat.blt n xs.length with
    | true  => xs[n]'(Nat.le_of_ble_eq_true h)
    | false => lctx (n - xs.length)

end push


section pop
  
  def popLCtxAt (pos : Nat) (lctx : Nat → α) (n : Nat) :=
    match pos.ble n with
    | true => lctx (.succ n)
    | false => lctx n
  
  theorem popLCtxAt.succ_zero (pos : Nat) (lctx : Nat → α) :
    popLCtxAt (.succ pos) lctx 0 = lctx 0 := rfl
  
  theorem popLCtxAt.succ_succ (pos : Nat) (lctx : Nat → α) (n : Nat) :
    popLCtxAt (.succ pos) lctx (.succ n) = popLCtxAt pos (fun n => lctx (.succ n)) n := rfl
  
  def popLCtxAt.comm (f : α → β) (pos : Nat) (lctx : Nat → α) (n : Nat) :
    f (popLCtxAt pos lctx n) = popLCtxAt pos (f ∘ lctx) n := by
    dsimp [popLCtxAt]
    match pos.ble n with
    | true => rfl
    | false => rfl
  
  def popLCtxAt.commFn (f : α → β) (pos : Nat) (lctx : Nat → α) :
    (fun n => f (popLCtxAt pos lctx n)) = (fun n => popLCtxAt pos (f ∘ lctx) n) :=
    funext (popLCtxAt.comm f pos lctx)
  
  def popLCtxAtDep {rty : Nat → α} {lctxty : α → Sort u}
    (pos : Nat) (lctx : ∀ n, lctxty (rty n)) (n : Nat) : lctxty (popLCtxAt pos rty n) := by
    dsimp [popLCtxAt]
    match pos.ble n with
    | true => exact lctx (.succ n)
    | false => exact lctx n
  
  theorem popLCtxAtDep.succ_zero {rty : Nat → α} {lctxty : α → Sort u}
    (lctx : ∀ n, lctxty (rty n)) (pos : Nat) :
    popLCtxAtDep (.succ pos) lctx 0 = lctx 0 := rfl
  
  theorem popLCtxAtDep.succ_succ {rty : Nat → α} {lctxty : α → Sort u}
    (pos : Nat) (lctx : ∀ n, lctxty (rty n)) (n : Nat) :
    popLCtxAtDep (.succ pos) lctx (.succ n) = popLCtxAtDep pos (fun n => lctx (.succ n)) n := rfl
  
  def popLCtxAtDep.absorbAux {rty : Nat → α} {lctxty : α → Sort u}
    (pos : Nat) (lctx : ∀ n, lctxty (rty n)) (n : Nat) : HEq
      (@popLCtxAtDep _ rty lctxty pos lctx n)
      (@popLCtxAtDep _ (lctxty ∘ rty) id pos lctx n) := by
    dsimp [popLCtxAt, popLCtxAtDep]
    match pos.ble n with
    | true => rfl
    | false => rfl
  
  def popLCtxAtDep.absorbAux' {rty : Nat → α} {lctxty : α → Sort u}
    (pos : Nat) (lctx : ∀ n, lctxty (rty n)) (n : Nat) : HEq
      (@popLCtxAtDep _ rty lctxty pos lctx n)
      (@popLCtxAtDep _ id (lctxty ∘ rty) pos lctx n) :=
    HEq.trans
      (b := @popLCtxAtDep _ (lctxty ∘ rty) id pos lctx n)
      (popLCtxAtDep.absorbAux pos lctx n)
      (HEq.symm (@popLCtxAtDep.absorbAux _ id (lctxty ∘ rty) pos lctx n))
  
  def popLCtxAtDep.absorb {rty : Nat → α} {lctxty : α → Sort u} (pos : Nat) (lctx : ∀ n, lctxty (rty n)):
    HEq (@popLCtxAtDep _ rty lctxty pos lctx) (@popLCtxAtDep _ (lctxty ∘ rty) id pos lctx) :=
    HEq.funext _ _ (popLCtxAtDep.absorbAux _ _)
  
  def popLCtxAtDep.comm {α : Sort w} {β : α → Sort x} {rty : Nat → α} {lctxty : α → Sort u}
    (f : ∀ (x : α), lctxty x → β x) (pos : Nat) (lctx : ∀ n, lctxty (rty n)) (n : Nat) :
      f _ (popLCtxAtDep pos lctx n) = popLCtxAtDep (lctxty:=β) pos (fun n => f _ (lctx n)) n := by
    dsimp [popLCtxAt, popLCtxAtDep]
    match pos.ble n with
    | true => rfl
    | false => rfl
  
  def popLCtxAtDep.commFn {α : Sort w} {β : α → Sort x} {rty : Nat → α} {lctxty : α → Sort u}
    (f : ∀ (x : α), lctxty x → β x) (pos : Nat) (lctx : ∀ n, lctxty (rty n)) :
    (fun n => f _ (popLCtxAtDep pos lctx n)) = (fun n => popLCtxAtDep (lctxty:=β) pos (fun n => f _ (lctx n)) n) :=
    funext (fun n => popLCtxAtDep.comm f pos lctx n)
  
  def popLCtxAt.commDep
    {β : α → Sort u} (f : ∀ (x : α), β x) (pos : Nat) (lctx : Nat → α) (n : Nat) :
      f (popLCtxAt pos lctx n) = popLCtxAtDep pos (fun n => f (lctx n)) n := by
    dsimp [popLCtxAt, popLCtxAtDep]
    match pos.ble n with
    | true => rfl
    | false => rfl

  def popLCtx (lctx : Nat → α) := popLCtxAt 0 lctx
  
  def popLCtx.comm (f : α → β) (lctx : Nat → α) (n : Nat) :
    f (popLCtx lctx n) = popLCtx (f ∘ lctx) n := popLCtxAt.comm f 0 lctx n
  
  def popLCtx.commFn (f : α → β) (lctx : Nat → α) :
    (fun n => f (popLCtx lctx n)) = (fun n => popLCtx (f ∘ lctx) n) :=
    popLCtxAt.commFn f 0 lctx
  
  def popLCtxDep {rty : Nat → α} {lctxty : α → Sort u}
    (lctx : ∀ n, lctxty (rty n)) : ∀ n, lctxty (popLCtx rty n) :=
    popLCtxAtDep 0 lctx
  
  def popLCtxDep.comm {α : Sort w} {β : α → Sort x} {rty : Nat → α} {lctxty : α → Sort u}
    (f : ∀ (x : α), lctxty x → β x) (lctx : ∀ n, lctxty (rty n)) (n : Nat) :
    f _ (popLCtxDep lctx n) = popLCtxDep (lctxty:=β) (fun n => f _ (lctx n)) n :=
    popLCtxAtDep.comm f 0 lctx n
  
  def popLCtxDep.absorbAux {rty : Nat → α} {lctxty : α → Sort u}
    (lctx : ∀ n, lctxty (rty n)) (n : Nat) : HEq
      (@popLCtxDep _ rty lctxty lctx n)
      (@popLCtxDep _ (lctxty ∘ rty) id lctx n) :=
      popLCtxAtDep.absorbAux 0 lctx n
  
  theorem popLCtxDep.absorb {rty : Nat → α} {lctxty : α → Sort u} (lctx : ∀ n, lctxty (rty n)) :
    HEq (@popLCtxDep _ rty lctxty lctx) (@popLCtxDep _ (lctxty ∘ rty) id lctx) :=
    popLCtxAtDep.absorb 0 lctx
  
  def popLCtxsAt (lvl pos : Nat) (lctx : Nat → α) (n : Nat) :=
    match pos.ble n with
    | true => lctx (Nat.add n lvl)
    | false => lctx n
  
  def popLCtxsAt.comm (f : α → β) (lvl pos : Nat) (lctx : Nat → α) (n : Nat) :
    f (popLCtxsAt lvl pos lctx n) = popLCtxsAt lvl pos (f ∘ lctx) n := by
    dsimp [popLCtxsAt]
    match Nat.ble pos n with
    | true => rfl
    | false => rfl
  
  def popLCtxsAt.succ_l (lvl pos : Nat) (lctx : Nat → α) (n : Nat) :
    popLCtxsAt (.succ lvl) pos lctx n = popLCtxsAt lvl pos (popLCtxAt pos lctx) n := by
    dsimp [popLCtxsAt, popLCtxAt]
    match h : Nat.ble pos n with
    | true =>
      dsimp
      have leAdd' := Nat.le_trans (Nat.le_of_ble_eq_true h) (Nat.le_add_right _ lvl)
      have bleAdd' := Nat.ble_eq_true_of_le leAdd'
      rw [bleAdd']; rfl
    | false => rfl
  
  def popLCtxsAt.succ_r (lvl pos : Nat) (lctx : Nat → α) (n : Nat) :
    popLCtxsAt (.succ lvl) pos lctx n = popLCtxAt pos (popLCtxsAt lvl pos lctx) n := by
    dsimp [popLCtxsAt, popLCtxAt]
    match h : Nat.ble pos n with
    | true =>
      dsimp
      dsimp
      have leAdd' := Nat.le_trans (Nat.le_of_ble_eq_true h) (Nat.le_add_right _ 1)
      have bleAdd' := Nat.ble_eq_true_of_le leAdd'
      rw [bleAdd', Nat.succ_add]; rfl
    | false => rfl
  
  def popLCtxsAt.one (pos : Nat) (lctx : Nat → α) :
    popLCtxsAt 1 pos lctx = popLCtxAt pos lctx := rfl

end pop


section push_pop

  def push_pop_eq (lctx : Nat → α) :
    pushLCtx (lctx 0) (popLCtx lctx) = lctx := by
    apply funext
    intro n; cases n
    case zero => rfl
    case succ n' => cases n' <;> rfl    
  
  def popAt_pushAt_eq (x : α) (pos : Nat) (lctx : Nat → α) (n : Nat) :
    popLCtxAt pos (pushLCtxAt x pos lctx) n = lctx n :=
    match pos, n with
    | 0, 0       => rfl
    | 0, .succ _ => rfl
    | .succ _, 0 => rfl
    | .succ pos' , .succ n' => by
      rw [popLCtxAt.succ_succ]; rw [pushLCtxAt.succ_succ_Fn];
      exact (popAt_pushAt_eq x pos' (fun n => lctx (.succ n)) n')
  
  def popAtDep_pushAtDep_eq
    {α : Sort w} {rty : Nat → α} {lctxty : α → Sort u}
    {xty : α} (x : lctxty xty) (pos : Nat) (lctx : ∀ n, lctxty (rty n)) (n : Nat) :
    HEq
      (@popLCtxAtDep _ (pushLCtxAt xty pos rty) lctxty
        pos (@pushLCtxAtDep _ rty lctxty xty x pos lctx) n)
      (lctx n) :=
    match pos, n with
    | 0, 0       => HEq.rfl
    | 0, .succ _ => HEq.rfl
    | .succ _, 0 => HEq.rfl
    | .succ pos' , .succ n' => by
      apply HEq.trans (heq_of_eq (popLCtxAtDep.succ_succ _ _ _))
      apply HEq.trans _ (popAtDep_pushAtDep_eq x pos' (fun n => lctx (.succ n)) n')
      apply (congr_arg₂_heq
        (γ := fun rty _ => lctxty (popLCtxAt pos' rty n'))
        (fun rty lctx => popLCtxAtDep (rty:=rty) pos' lctx n') _ _)
      apply pushLCtxAt.succ_succ_Fn
      apply pushLCtxAtDep.succ_succ_Fn

end push_pop


section generic

  def mapAt (pos : Nat) (f : Nat → Nat) (n : Nat) :=
    match pos.ble n with
    | true => f (n - pos) + pos
    | false => n
  
  def restoreAt (pos : Nat) (restore : ∀ {α}, (Nat → α) → (Nat → α)) :=
    fun {α} (lctx : Nat → α) (n : Nat) =>
      match pos.ble n with
      | true => restore (fun i => lctx (i + pos)) (n - pos)
      | false => lctx n

  theorem restoreAt.succ_succ (pos : Nat) (restore : ∀ {α}, (Nat → α) → (Nat → α))
    {α} (lctx : Nat → α) (n : Nat) :
    restoreAt (.succ pos) restore lctx (.succ n) = restoreAt pos restore (fun n => lctx (.succ n)) n := by
    dsimp [restoreAt, Nat.ble]; rw [Nat.succ_sub_succ]; rfl

  theorem restoreAt.succ_pushLCtx (restore : ∀ {α}, (Nat → α) → (Nat → α))
    (x : α) (pos : Nat) (lctx : Nat → α) (n : Nat) :
    restoreAt (.succ pos) restore (pushLCtx x lctx) n = pushLCtx x (restoreAt pos restore lctx) n :=
    match pos, n with
    | 0,          0        => rfl
    | 0,          .succ _  => rfl
    | .succ _,    0        => rfl
    | .succ pos', .succ n' => by
      rw [restoreAt.succ_succ]
      rw [pushLCtx.succ, pushLCtx.succ_Fn]

  theorem restoreAt.succ_pushLCtx_Fn (restore : ∀ {α}, (Nat → α) → (Nat → α))
    (x : α) (pos : Nat) (lctx : Nat → α) :
    restoreAt (.succ pos) restore (pushLCtx x lctx) = pushLCtx x (restoreAt pos restore lctx) :=
    funext (fun n => restoreAt.succ_pushLCtx restore x pos lctx n)

  def covPair (f : Nat → Nat) (restore : ∀ {α}, (Nat → α) → (Nat → α)) :=
    ∀ {α} (lctx : Nat → α) (n : Nat), (restore lctx) (f n) = lctx n
  
  def covPairAt (f : Nat → Nat) (restore : ∀ {α}, (Nat → α) → (Nat → α)) :=
    ∀ {α} (pos : Nat) (lctx : Nat → α) (n : Nat),
      (restoreAt pos restore lctx) (mapAt pos f n) = lctx n
  
  theorem covPairAt.ofCovPair (cp : covPair f restore) : covPairAt f restore := by
    intros α pos lctx n;
    dsimp [restoreAt, mapAt]
    match h : pos.ble n with
    | true =>
      dsimp;
      have heq : Nat.ble pos (f (n - pos) + pos) = true := by
        apply Nat.ble_eq_true_of_le;
        apply Nat.le_add_left
      rw [heq]; dsimp
      rw [Nat.add_sub_assoc]; rw [Nat.sub_self]; dsimp
      rw [cp]; rw [Nat.sub_add_cancel (Nat.le_of_ble_eq_true h)]
      constructor
    | false => dsimp; rw [h]

  def restoreAtDep (pos : Nat) {restore : ∀ {α}, (Nat → α) → (Nat → α)}
    (restoreDep : ∀ {rty : Nat → α} {lctxty : α → Sort u}, (∀ n, lctxty (rty n)) → ∀ n, lctxty (restore rty n))
    {rty : Nat → α} {lctxty : α → Sort u} (lctx : ∀ n, lctxty (rty n)) (n : Nat) : lctxty (restoreAt pos restore rty n) := by
    dsimp [restoreAt]
    match Nat.ble pos n with
    | true  => exact (restoreDep (fun i => lctx (i + pos)) (n - pos))
    | false => exact (lctx n)

  theorem restoreAtDep.succ_succ (pos : Nat) {restore : ∀ {α}, (Nat → α) → (Nat → α)}
    (restoreDep : ∀ {α} {rty : Nat → α} {lctxty : α → Sort u}, (∀ n, lctxty (rty n)) → ∀ n, lctxty (restore rty n))
    {rty : Nat → α} {lctxty : α → Sort u} (lctx : ∀ n, lctxty (rty n)) (n : Nat) :
    HEq (restoreAtDep (.succ pos) restoreDep lctx (.succ n)) (restoreAtDep pos restoreDep (fun n => lctx (.succ n)) n) := by
    dsimp [restoreAt, restoreAtDep, Nat.ble]; rw [Nat.succ_sub_succ]; rfl

  theorem restoreAtDep.succ_pushLCtxDep
    (restore : ∀ {α}, (Nat → α) → (Nat → α))
    (restoreDep : ∀ {α} {rty : Nat → α} {lctxty : α → Sort u}, (∀ n, lctxty (rty n)) → ∀ n, lctxty ((restore rty) n))
    {rty : Nat → α} {lctxty : α → Sort u} {xty : α} (x : lctxty xty) (pos : Nat)
    (lctx : ∀ n, lctxty (rty n)) (n : Nat) :
    HEq (restoreAtDep (.succ pos) restoreDep (pushLCtxDep x lctx) n) (pushLCtxDep x (restoreAtDep pos restoreDep lctx) n) :=
    match pos, n with
    | 0,          0        => HEq.rfl
    | 0,          .succ _  => HEq.rfl
    | .succ _,    0        => HEq.rfl
    | .succ pos', .succ n' => by
      apply HEq.trans (restoreAtDep.succ_succ (Nat.succ pos') restoreDep (pushLCtxDep x lctx) n')
      rw [pushLCtxDep.succ]; rw [pushLCtxDep.succ_Fn]

  theorem restoreAtDep.succ_pushLCtxDep_Fn
    (restore : ∀ {α}, (Nat → α) → (Nat → α))
    (restoreDep : ∀ {α} {rty : Nat → α} {lctxty : α → Sort u}, (∀ n, lctxty (rty n)) → ∀ n, lctxty ((restore rty) n))
    {rty : Nat → α} {lctxty : α → Sort u} {xty : α} (x : lctxty xty) (pos : Nat)
    (lctx : ∀ n, lctxty (rty n)) :
    HEq (restoreAtDep (.succ pos) restoreDep (pushLCtxDep x lctx)) (pushLCtxDep x (restoreAtDep pos restoreDep lctx)) :=
    HEq.funext _ _ (fun n => restoreAtDep.succ_pushLCtxDep restore restoreDep x pos lctx n)

  def covPairDep
    (f : Nat → Nat) (restore : ∀ {α}, (Nat → α) → (Nat → α))
    (restoreDep : ∀ {α} {rty : Nat → α} {lctxty : α → Sort u}, (∀ n, lctxty (rty n)) → ∀ n, lctxty ((restore rty) n)) :=
    covPair f restore ∧
      ∀ {α} {rty : Nat → α} {lctxty : α → Sort u} (lctx : ∀ n, lctxty (rty n)) (n : Nat),
        HEq (@restoreDep _ rty lctxty lctx (f n)) (lctx n)

  def covPairDepAt
    (f : Nat → Nat) (restore : ∀ {α}, (Nat → α) → (Nat → α))
    (restoreDep : ∀ {α} {rty : Nat → α} {lctxty : α → Sort u}, (∀ n, lctxty (rty n)) → ∀ n, lctxty ((restore rty) n)) :=
    covPairAt f restore ∧
      ∀ {α} (pos : Nat) {rty : Nat → α} {lctxty : α → Sort u} (lctx : ∀ n, lctxty (rty n)) (n : Nat),
        HEq (restoreAtDep pos restoreDep (rty:=rty) lctx (mapAt pos f n)) (lctx n)

  theorem covPairDepAt.ofCovPairDep (cpd : covPairDep f restore restoreDep) :
    covPairDepAt f restore restoreDep := by
    apply And.intro
    case left => exact covPairAt.ofCovPair cpd.left
    case right =>
      intros α pos rty lctxty lctx n
      dsimp [restoreAt, restoreAtDep, mapAt]
      match h : pos.ble n with
      | true =>
        dsimp;
        have heq : Nat.ble pos (f (n - pos) + pos) = true := by
          apply Nat.ble_eq_true_of_le;
          apply Nat.le_add_left
        have hle := Nat.le_of_ble_eq_true h
        rw [heq]; dsimp
        rw [Nat.add_sub_assoc .refl]; rw [Nat.sub_self]; dsimp
        apply HEq.trans (b:=lctx (n - pos + pos))
        case h₁ => apply cpd.right
        case h₂ => rw [Nat.sub_add_cancel hle]
      | false => dsimp; rw [h]

end generic

end Auto.Embedding