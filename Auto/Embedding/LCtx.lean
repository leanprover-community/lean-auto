import Auto.Lib.BoolExtra
import Auto.Lib.HEqExtra
import Auto.Lib.NatExtra
import Auto.Lib.ListExtra
import Auto.Lib.HList
import Std.Data.List.Lemmas

namespace Auto.Embedding

section generic

  @[reducible] def mapAt (pos : Nat) (f : Nat → Nat) (n : Nat) :=
    match pos.ble n with
    | true => f (n - pos) + pos
    | false => n

  theorem mapAt_id_eq_id (pos : Nat) : mapAt pos id = id := by
    apply funext; intros n;
    dsimp [mapAt]
    match h : pos.ble n with
    | true =>
      dsimp
      rw [Nat.sub_add_cancel (Nat.le_of_ble_eq_true h)]
    | false => rfl
  
  theorem mapAt_id_eq_id' (pos : Nat) : mapAt pos (fun x => x) = id :=
    mapAt_id_eq_id pos

  theorem mapAt.zero (f : Nat → Nat) : mapAt 0 f = f :=
    funext (fun n => match n with | 0 => rfl | _ + 1 => rfl)

  theorem mapAt.succ_zero (pos : Nat) (f : Nat → Nat) :
    mapAt (.succ pos) f 0 = 0 := rfl

  theorem mapAt.succ_succ (pos : Nat) (f : Nat → Nat) (n : Nat) :
    mapAt (.succ pos) f (.succ n) = .succ (mapAt pos f n) := by
    dsimp [mapAt, Nat.ble]
    match Nat.ble pos n with
    | true => dsimp; rw [Nat.succ_sub_succ]; rfl
    | false => rfl

  theorem mapAt.comp (pos : Nat) (g f : Nat → Nat) (n : Nat) :
    mapAt pos (fun x => g (f x)) n = mapAt pos g (mapAt pos f n) := by
    dsimp [mapAt]
    match h : Nat.ble pos n with
    | true =>
      dsimp;
      have hble : ∀ t, Nat.ble pos (t + pos) = true := by
        intro t; apply Nat.ble_eq_true_of_le;
        apply Nat.le_add_left
      rw [hble]; dsimp; rw [Nat.add_sub_cancel]
    | false =>
      dsimp; rw [h]
  
  @[reducible] def restoreAt {α} (pos : Nat) (restore : (Nat → α) → (Nat → α)) :=
    fun (lctx : Nat → α) (n : Nat) =>
      match pos.ble n with
      | true => restore (fun i => lctx (i + pos)) (n - pos)
      | false => lctx n

  theorem restoreAt.zero {α} (restore : (Nat → α) → (Nat → α)) :
    restoreAt 0 restore = restore := by
    apply funext; intro lctx; apply funext; intro n;
    cases n <;> rfl

  theorem restoreAt.succ_succ {α} (pos : Nat) (restore : (Nat → α) → (Nat → α))
    (lctx : Nat → α) (n : Nat) :
    restoreAt (.succ pos) restore lctx (.succ n) = restoreAt pos restore (fun n => lctx (.succ n)) n := by
    dsimp [restoreAt, Nat.ble]; rw [Nat.succ_sub_succ]; rfl

  theorem restoreAt.succ_succ_Fn {α} (pos : Nat)
    (restore : (Nat → α) → (Nat → α)) (lctx : Nat → α) :
    (fun n => restoreAt (.succ pos) restore lctx (.succ n)) = restoreAt pos restore (fun n => lctx (.succ n)) :=
    funext (fun n => restoreAt.succ_succ pos restore lctx n)

  def covPair {α} (f : Nat → Nat) (restore : (Nat → α) → (Nat → α)) :=
    ∀ (lctx : Nat → α) (n : Nat), (restore lctx) (f n) = lctx n
  
  def covPairAt {α} (f : Nat → Nat) (restore : (Nat → α) → (Nat → α)) :=
    ∀ (pos : Nat) (lctx : Nat → α) (n : Nat),
      (restoreAt pos restore lctx) (mapAt pos f n) = lctx n
  
  theorem covPairAt.ofCovPair (cp : covPair f restore) : covPairAt f restore := by
    intros pos lctx n;
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

  def restoreAtDep {α} {lctxty : α → Sort u}
    (pos : Nat) {restore : (Nat → α) → (Nat → α)}
    (restoreDep : ∀ {rty : Nat → α}, (∀ n, lctxty (rty n)) → ∀ n, lctxty (restore rty n))
    {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) (n : Nat) : lctxty (restoreAt pos restore rty n) := by
    dsimp [restoreAt]
    match Nat.ble pos n with
    | true  => exact (restoreDep (fun i => lctx (i + pos)) (n - pos))
    | false => exact (lctx n)

  theorem restoreAtDep.zero {α} {lctxty : α → Sort u}
    {restore : (Nat → α) → (Nat → α)}
    (restoreDep : ∀ {rty : Nat → α}, (∀ n, lctxty (rty n)) → ∀ n, lctxty (restore rty n))
    {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) :
    HEq (restoreAtDep 0 restoreDep lctx) (restoreDep (rty:=rty) lctx) := by
    apply HEq.funext; intros n; cases n <;> rfl

  theorem restoreAtDep.succ_succ {α} {lctxty : α → Sort u}
    (pos : Nat) {restore : (Nat → α) → (Nat → α)}
    (restoreDep : ∀ {rty : Nat → α}, (∀ n, lctxty (rty n)) → ∀ n, lctxty (restore rty n))
    {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) (n : Nat) :
    HEq (restoreAtDep (.succ pos) restoreDep lctx (.succ n)) (restoreAtDep pos restoreDep (fun n => lctx (.succ n)) n) := by
    dsimp [restoreAt, restoreAtDep, Nat.ble]; rw [Nat.succ_sub_succ]; rfl

  theorem restoreAtDep.succ_succ_Fn {α} {lctxty : α → Sort u}
    (pos : Nat) {restore : (Nat → α) → (Nat → α)}
    (restoreDep : ∀ {rty : Nat → α}, (∀ n, lctxty (rty n)) → ∀ n, lctxty (restore rty n))
    {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) :
    HEq (fun n => restoreAtDep (.succ pos) restoreDep lctx (.succ n)) (restoreAtDep pos restoreDep (fun n => lctx (.succ n))) :=
    HEq.funext _ _ (fun n => restoreAtDep.succ_succ pos restoreDep lctx n)

  def covPairDep {α} (lctxty : α → Sort u)
    (f : Nat → Nat) (restore : (Nat → α) → (Nat → α))
    (restoreDep : ∀ {rty : Nat → α}, (∀ n, lctxty (rty n)) → ∀ n, lctxty ((restore rty) n)) :=
    covPair f restore ∧
      ∀ {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) (n : Nat),
        HEq (@restoreDep rty lctx (f n)) (lctx n)

  def covPairDepAt {α} (lctxty : α → Sort u)
    (f : Nat → Nat) (restore : (Nat → α) → (Nat → α))
    (restoreDep : ∀ {rty : Nat → α}, (∀ n, lctxty (rty n)) → ∀ n, lctxty ((restore rty) n)) :=
    covPairAt f restore ∧
      ∀ (pos : Nat) {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) (n : Nat),
        HEq (restoreAtDep pos restoreDep (rty:=rty) lctx (mapAt pos f n)) (lctx n)

  theorem covPairDepAt.ofCovPairDep (cpd : covPairDep lctxty f restore restoreDep) :
    covPairDepAt lctxty f restore restoreDep := by
    apply And.intro
    case left => exact covPairAt.ofCovPair cpd.left
    case right =>
      intros pos rty lctx n
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


section push
  
  @[reducible] def pushLCtx (x : α) (lctx : Nat → α) (n : Nat) : α :=
    match n with
    | 0 => x
    | n' + 1 => lctx n'

  @[reducible] def pushLCtxAt (x : α) (pos : Nat) := restoreAt pos (pushLCtx x)

  theorem pushLCtxAt.zero (x : α) : pushLCtxAt x 0 = pushLCtx x := restoreAt.zero _

  theorem pushLCtxAt.succ_zero (x : α) (pos : Nat) (lctx : Nat → α) :
    pushLCtxAt x (.succ pos) lctx 0 = lctx 0 := rfl
  
  theorem pushLCtxAt.succ_succ (x : α) (pos : Nat) (lctx : Nat → α) (n : Nat) :
    pushLCtxAt x (.succ pos) lctx (.succ n) = pushLCtxAt x pos (fun n => lctx (.succ n)) n :=
    restoreAt.succ_succ _ _ _ _
  
  theorem pushLCtxAt.succ_succ_Fn (x : α) (pos : Nat) (lctx : Nat → α) :
    (fun n => pushLCtxAt x (.succ pos) lctx (.succ n)) = pushLCtxAt x pos (fun n => lctx (.succ n)) :=
    restoreAt.succ_succ_Fn _ _ _
  
  def pushLCtxAt.comm (f : α → β) (x : α) (pos : Nat) (lctx : Nat → α) (n : Nat) :
    f (pushLCtxAt x pos lctx n) = pushLCtxAt (f x) pos (f ∘ lctx) n := by
    dsimp [pushLCtxAt, restoreAt]
    match pos.ble n with
    | true =>
      match (n - pos) with
      | 0 => rfl
      | _ + 1 => rfl
    | false => rfl
  
  theorem pushLCtxAt.commFn (f : α → β) (x : α) (pos : Nat) (lctx : Nat → α) :
    (fun n => f (pushLCtxAt x pos lctx n)) = (fun n => pushLCtxAt (f x) pos (fun n => f (lctx n)) n) :=
    funext (pushLCtxAt.comm f x pos lctx)
  
  @[reducible] def pushLCtxDep {lctxty : α → Sort u} {xty : α} (x : lctxty xty)
    {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) (n : Nat) : lctxty (pushLCtx xty rty n) := by
    dsimp [pushLCtx]
    match n with
    | 0 => exact x
    | n' + 1 => exact (lctx n')

  def pushLCtxAtDep {lctxty : α → Sort u} {xty : α} (x : lctxty xty) (pos : Nat)
    {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) (n : Nat) : lctxty (pushLCtxAt xty pos rty n) :=
    restoreAtDep pos (pushLCtxDep x) lctx n
  
  theorem pushLCtxAtDep.zero {lctxty : α → Sort u} {xty : α} (x : lctxty xty)
    {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) :
    HEq (pushLCtxAtDep x 0 lctx) (pushLCtxDep x lctx) := restoreAtDep.zero _ _

  theorem pushLCtxAtDep.succ_zero {rty : Nat → α} {lctxty : α → Sort u}
    {xty : α} (x : lctxty xty) (pos : Nat) (lctx : ∀ n, lctxty (rty n)) :
    pushLCtxAtDep x (.succ pos) lctx 0 = lctx 0 := rfl
  
  theorem pushLCtxAtDep.succ_succ {rty : Nat → α} {lctxty : α → Sort u} {xty : α}
    (x : lctxty xty) (pos : Nat) (lctx : ∀ n, lctxty (rty n)) (n : Nat) :
    HEq (pushLCtxAtDep x (.succ pos) lctx (.succ n)) (pushLCtxAtDep x pos (fun n => lctx (.succ n)) n) :=
    restoreAtDep.succ_succ _ _ _ _
  
  theorem pushLCtxAtDep.succ_succ_Fn {rty : Nat → α} {lctxty : α → Sort u}
    {xty : α} (x : lctxty xty) (pos : Nat) (lctx : ∀ n, lctxty (rty n)) :
    HEq (fun n => pushLCtxAtDep x (.succ pos) lctx (.succ n)) (pushLCtxAtDep x pos (fun n => lctx (.succ n))) :=
    restoreAtDep.succ_succ_Fn _ _ _
  
  def pushLCtxAtDep.comm {α : Sort w} {β : α → Sort x} {rty : Nat → α} {lctxty : α → Sort u}
    (f : ∀ (x : α), lctxty x → β x) {xty : α} (x : lctxty xty) (pos : Nat)
    (lctx : ∀ n, lctxty (rty n)) (n : Nat) :
      f _ (pushLCtxAtDep x pos lctx n) = pushLCtxAtDep (lctxty:=β) (f xty x) pos (fun n => f _ (lctx n)) n := by
    dsimp [pushLCtxAt, pushLCtxAtDep, restoreAt, restoreAtDep]
    match pos.ble n with
    | true =>
      match (n - pos) with
      | 0 => rfl
      | _ + 1 => rfl
    | false => rfl
  
  def pushLCtxAtDep.nonDep {rty : Nat → α} {lctxty : Sort u}
    {xty : α} (x : lctxty) (pos : Nat) (lctx : Nat → lctxty) (n : Nat) :
    @pushLCtxAtDep _ (fun _ => lctxty) xty x pos rty lctx n = pushLCtxAt x pos lctx n := rfl
  
  def pushLCtxAtDep.absorbAux {rty : Nat → α} {lctxty : α → Sort u}
    {xty : α} (x : lctxty xty) (pos : Nat) (lctx : ∀ n, lctxty (rty n)) (n : Nat) :
    HEq
      (@pushLCtxAtDep _ lctxty _ x pos rty lctx n)
      (@pushLCtxAtDep _ id _ x pos (lctxty ∘ rty) lctx n) := by
    dsimp [pushLCtxAt, pushLCtxAtDep]
    dsimp [pushLCtxAt, pushLCtxAtDep, restoreAt, restoreAtDep]
    match pos.ble n with
    | true =>
      match (n - pos) with
      | 0 => rfl
      | _ + 1 => rfl
    | false => rfl
  
  theorem pushLCtxAtDep.absorb {rty : Nat → α} {lctxty : α → Sort u}
    {xty : α} (x : lctxty xty) (pos : Nat) (lctx : ∀ n, lctxty (rty n)) :
    HEq (@pushLCtxAtDep _ lctxty _ x pos rty lctx) (@pushLCtxAtDep _ id _ x pos (lctxty ∘ rty) lctx) :=
    HEq.funext _ _ (pushLCtxAtDep.absorbAux _ _ _)
  
  def pushLCtx.zero (x : α) (lctx : Nat → α) : pushLCtx x lctx 0 = x := rfl
  
  def pushLCtx.succ (x : α) (lctx : Nat → α) (n : Nat) : pushLCtx x lctx (.succ n) = lctx n := rfl
  
  def pushLCtx.succ_Fn (x : α) (lctx : Nat → α) :
    (fun n => pushLCtx x lctx (.succ n)) = lctx := rfl
  
  def pushLCtx.comm (f : α → β) (x : α) (lctx : Nat → α) (n : Nat) :
    f (pushLCtx x lctx n) = pushLCtx (f x) (fun n => f (lctx n)) n := by
    rw [← pushLCtxAt.zero]; rw [← pushLCtxAt.zero]
    apply pushLCtxAt.comm f x 0 lctx n
  
  theorem pushLCtx.commFn (f : α → β) (x : α) (lctx : Nat → α) :
    (fun n => f (pushLCtx x lctx n)) = (fun n => pushLCtx (f x) (fun n => f (lctx n)) n) :=
    funext (pushLCtx.comm f x lctx)
  
  def pushLCtx_pushLCtxAt (x y : α) (pos : Nat) (lctx : Nat → α) :
    pushLCtx y (pushLCtxAt x pos lctx) = pushLCtxAt x (Nat.succ pos) (pushLCtx y lctx) := by
    apply funext; intro n; cases n; rfl; rw [pushLCtxAt.succ_succ];
  
  def pushLCtxDep.zero {lctxty : α → Sort u} {xty : α} (x : lctxty xty)
    {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) :
    pushLCtxDep x lctx 0 = x := rfl
  
  def pushLCtxDep.succ {lctxty : α → Sort u}
    {xty : α} (x : lctxty xty) {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) (n : Nat) :
    pushLCtxDep x lctx (.succ n) = lctx n := rfl

  def pushLCtxDep.succ_Fn {lctxty : α → Sort u}
    {xty : α} (x : lctxty xty) {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) :
    (fun n => pushLCtxDep x lctx (.succ n)) = lctx := rfl
  
  def pushLCtxDep.comm {α : Sort w} {β : α → Sort x} {rty : Nat → α} {lctxty : α → Sort u}
    (f : ∀ (x : α), lctxty x → β x) (lctx : ∀ n, lctxty (rty n))
    {xty : α} (x : lctxty xty) (n : Nat) :
    f _ (pushLCtxDep x lctx n) = pushLCtxDep (lctxty:=β) (f xty x) (fun n => f _ (lctx n)) n := by
    dsimp [pushLCtx, pushLCtxDep]
    cases n <;> rfl
  
  def pushLCtxDep.absorbAux {rty : Nat → α} {lctxty : α → Sort u}
    (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) (n : Nat) :
    HEq
      (@pushLCtxDep _ lctxty _ x rty lctx n)
      (@pushLCtxDep _ id _ x (lctxty ∘ rty) lctx n) := by
    dsimp [pushLCtx, pushLCtxDep]
    cases n <;> rfl
  
  theorem pushLCtxDep.absorb {rty : Nat → α} {lctxty : α → Sort u}
    (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) :
    HEq (@pushLCtxDep _ lctxty _ x rty lctx) (@pushLCtxDep _ id _ x (lctxty ∘ rty) lctx) :=
    HEq.funext _ _ (fun n => pushLCtxDep.absorbAux lctx x n)
  
  def pushLCtxDep_pushLCtxAtDep {rty : Nat → α} {lctxty : α → Sort u}
    (lctx : ∀ n, lctxty (rty n)) {xty : α} (x : lctxty xty) {yty : α} (y : lctxty yty) (pos : Nat) :
    HEq (pushLCtxDep y (pushLCtxAtDep x pos lctx)) (pushLCtxAtDep x (Nat.succ pos) (pushLCtxDep y lctx)) := by
    apply HEq.funext; intro n; cases n; rfl;
    apply HEq.trans _ (HEq.symm (pushLCtxAtDep.succ_succ _ _ _ _)); apply HEq.rfl

  @[reducible] def pushLCtxs (xs : List α) (lctx : Nat → α) (n : Nat) : α :=
    match Nat.blt n xs.length with
    | true  => xs.getD n (lctx 0)
    | false => lctx (n - xs.length)

  theorem pushLCtxs.nil (lctx : Nat → α) :
    pushLCtxs .nil lctx = lctx := rfl

  theorem pushLCtxs.cons (xs : List α) (lctx : Nat → α) :
    pushLCtxs (x :: xs) lctx = pushLCtx x (pushLCtxs xs lctx) := by
    apply funext; intros n; cases n
    case h.zero =>
      dsimp [pushLCtxs, pushLCtx, Nat.blt, Nat.ble]
      rw [Nat.ble_eq_true_of_le]; rfl
      apply Nat.zero_le
    case h.succ n =>
      dsimp [pushLCtxs, pushLCtx, Nat.blt, Nat.ble]
      rw [Nat.succ_sub_succ]; rfl

  theorem pushLCtxs.append (xs ys : List α) (lctx : Nat → α) :
    pushLCtxs (xs ++ ys) lctx = pushLCtxs xs (pushLCtxs ys lctx) := by
    induction xs;
    case nil => rfl
    case cons x xs IH =>
      dsimp; rw [pushLCtxs.cons]; rw [pushLCtxs.cons]; rw [IH]

  theorem pushLCtxs.singleton (x : α) (lctx : Nat → α) :
    pushLCtxs [x] lctx = pushLCtx x lctx := pushLCtxs.cons [] lctx

  theorem pushLCtxs.cons_zero (xs : List α) (lctx : Nat → α) :
    pushLCtxs (x :: xs) lctx 0 = x := by
    dsimp [pushLCtxs, Nat.blt, Nat.ble];
    rw [Nat.ble_eq_true_of_le]; rfl
    apply Nat.zero_le

  theorem pushLCtxs.cons_succ (xs : List α) (lctx : Nat → α) (n : Nat) :
    pushLCtxs (x :: xs) lctx (.succ n) = pushLCtxs xs lctx n := by
    dsimp [pushLCtxs]; rw [Nat.succ_sub_succ]; rfl

  theorem pushLCtxs.cons_succ_Fn (xs : List α) (lctx : Nat → α) :
    (fun n => pushLCtxs (x :: xs) lctx (.succ n)) = pushLCtxs xs lctx :=
    funext (fun n => pushLCtxs.cons_succ xs lctx n)

  theorem pushLCtxs.append_add
    (xs ys : List α) (lctx : Nat → α)
    (val : Nat) (heq : xs.length = val) (n : Nat) :
    pushLCtxs (xs ++ ys) lctx (n + val) = pushLCtxs ys lctx n := by
    dsimp [pushLCtxs]; rw [List.length_append]
    have heq₁ : Nat.blt (n + val) (List.length xs + List.length ys) = Nat.blt n (List.length ys) := by
      dsimp [Nat.blt]; rw [heq];
      rw [Nat.add_comm val]; rw [← Nat.succ_add]
      exact Eq.symm (Nat.ble_add _ _ _)
    rw [heq₁]
    have heq₂ : n + val - (List.length xs + List.length ys) = n - List.length ys := by
      rw [heq]; rw [Nat.add_comm val]; rw [Nat.add_sub_add_right]
    rw [heq₂]
    dsimp [List.getD]; rw [List.get?_append_right]
    case _ => rw [heq]; rw [Nat.add_sub_cancel]
    case _ => rw [heq]; apply Nat.le_add_left

  @[reducible] def pushLCtxsAt (xs : List α) (pos : Nat) :=
    restoreAt pos (pushLCtxs xs)

  theorem pushLCtxsAt.zero (xs : List α) : pushLCtxsAt xs 0 = pushLCtxs xs :=
    restoreAt.zero _

  theorem pushLCtxsAt.succ_zero (xs : List α) (pos : Nat) (lctx : Nat → α) :
    pushLCtxsAt xs (.succ pos) lctx 0 = lctx 0 := rfl

  theorem pushLCtxsAt.succ_succ (xs : List α) (pos : Nat) (lctx : Nat → α) (n : Nat) :
    pushLCtxsAt xs (.succ pos) lctx (.succ n) = pushLCtxsAt xs pos (fun n => lctx (.succ n)) n := by
    dsimp [pushLCtxsAt]; rw [restoreAt.succ_succ]

  theorem pushLCtxsAt.succ_succ_Fn (xs : List α) (pos : Nat) (lctx : Nat → α) :
    (fun n => pushLCtxsAt xs (.succ pos) lctx (.succ n)) = pushLCtxsAt xs pos (fun n => lctx (.succ n)) := by
    dsimp [pushLCtxsAt]; rw [restoreAt.succ_succ_Fn]

  @[reducible] def pushLCtxsDep
    {lctxty : α → Sort u} {tys : List α} (xs : HList lctxty tys)
    {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) (n : Nat) :
    lctxty (pushLCtxs tys rty n) := by
    dsimp [pushLCtxs]
    match Nat.blt n tys.length with
    | true  => exact (xs.getD (α:=α) (lctx 0) n)
    | false => exact (lctx (n - tys.length))

  theorem pushLCtxsDep.heq
    {lctxty₁ : α₁ → Sort u} {tys₁ : List α₁} (xs₁ : HList lctxty₁ tys₁)
    (rty₁ : Nat → α₁) (lctx₁ : ∀ n, lctxty₁ (rty₁ n)) (n₁ : Nat)
    {lctxty₂ : α₂ → Sort u} {tys₂ : List α₂} (xs₂ : HList lctxty₂ tys₂)
    (rty₂ : Nat → α₂) (lctx₂ : ∀ n, lctxty₂ (rty₂ n)) (n₂ : Nat)
    (h₁ : α₁ = α₂) (h₂ : HEq lctxty₁ lctxty₂) (h₃ : HEq tys₁ tys₂)
    (h₄ : HEq xs₁ xs₂) (h₅ : HEq rty₁ rty₂) (h₆ : HEq lctx₁ lctx₂) (h₇ : n₁ = n₂):
    HEq (pushLCtxsDep xs₁ lctx₁ n₁) (pushLCtxsDep xs₂ lctx₂ n₂) := by
    cases h₁; cases h₂; cases h₃; cases h₄; cases h₅; cases h₆; cases h₇; apply HEq.rfl

  theorem pushLCtxsDep.nil
    {lctxty : α → Sort u} {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) :
    pushLCtxsDep .nil lctx = lctx := rfl

  theorem pushLCtxsDep.cons
    {lctxty : α → Sort u} {ty : α} (x : lctxty ty) {tys : List α}
    (xs : HList lctxty tys) {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) :
    HEq (pushLCtxsDep (.cons x xs) lctx) (pushLCtxDep x (pushLCtxsDep xs lctx)) := by
    apply HEq.funext; intros n; cases n
    case zero =>
      dsimp [pushLCtxs, pushLCtx, Nat.blt, Nat.ble]
      rw [Nat.ble_eq_true_of_le]; rfl
      apply Nat.zero_le
    case succ n =>
      dsimp [pushLCtxs, pushLCtx, Nat.blt, Nat.ble]
      rw [Nat.succ_sub_succ]; rfl

  theorem pushLCtxsDep.singleton
    {lctxty : α → Sort u} {ty : α} (x : lctxty ty)
    {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) :
    HEq (pushLCtxsDep (.cons x .nil) lctx) (pushLCtxDep x lctx) := pushLCtxsDep.cons x .nil lctx
  
  theorem pushLCtxsDep.cons_zero
    {lctxty : α → Sort u} {ty : α} (x : lctxty ty) {tys : List α}
    (xs : HList lctxty tys) {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) :
    HEq (pushLCtxsDep (.cons x xs) lctx 0) x := by
    dsimp [pushLCtxs, Nat.blt, Nat.ble];
    rw [Nat.ble_eq_true_of_le]; rfl
    apply Nat.zero_le

  theorem pushLCtxsDep.cons_succ
    {lctxty : α → Sort u} {ty : α} (x : lctxty ty) {tys : List α}
    (xs : HList lctxty tys) {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) (n : Nat) :
    HEq (pushLCtxsDep (.cons x xs) lctx (.succ n)) (pushLCtxsDep xs lctx n) := by
    dsimp [pushLCtxs]; rw [Nat.succ_sub_succ]; rfl

  theorem pushLCtxsDep.cons_succ_Fn
    {lctxty : α → Sort u} {ty : α} (x : lctxty ty) {tys : List α}
    (xs : HList lctxty tys) {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) :
    HEq (fun n => pushLCtxsDep (.cons x xs) lctx (.succ n)) (pushLCtxsDep xs lctx) :=
    HEq.funext _ _ (fun n => pushLCtxsDep.cons_succ x xs lctx n)

  @[reducible] def pushLCtxsAtDep
    {lctxty : α → Sort u} {tys : List α} (xs : HList lctxty tys) (pos : Nat)
    {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) :=
    restoreAtDep pos (pushLCtxsDep xs) lctx

  theorem pushLCtxsAtDep.zero
    {lctxty : α → Sort u} {tys : List α} (xs : HList lctxty tys)
    {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) :
    HEq (pushLCtxsAtDep xs 0 lctx) (pushLCtxsDep xs lctx) := restoreAtDep.zero _ _

  theorem pushLCtxsAtDep.succ_zero
    {lctxty : α → Sort u} {tys : List α} (xs : HList lctxty tys)
    {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) :
    pushLCtxsAtDep xs (.succ pos) lctx 0 = lctx 0 := rfl

  theorem pushLCtxsAtDep.succ_succ 
    {lctxty : α → Sort u} {tys : List α} (xs : HList lctxty tys) (pos : Nat)
    {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) (n : Nat) :
    HEq (pushLCtxsAtDep xs (.succ pos) lctx (.succ n)) (pushLCtxsAtDep xs pos (fun n => lctx (.succ n)) n) := by
    dsimp [pushLCtxsAtDep]; apply restoreAtDep.succ_succ

  theorem pushLCtxsAtDep.succ_succ_Fn 
    {lctxty : α → Sort u} {tys : List α} (xs : HList lctxty tys) (pos : Nat)
    {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) :
    HEq (fun n => pushLCtxsAtDep xs (.succ pos) lctx (.succ n)) (pushLCtxsAtDep xs pos (fun n => lctx (.succ n))) := by
    dsimp [pushLCtxsAtDep]; apply restoreAtDep.succ_succ_Fn

  theorem List.ofFun_get?_eq_none (f : Nat → α) (n m : Nat) (h : n ≤ m) :
    (List.ofFun f n).get? m = .none := by
    revert f n; induction m <;> intros f n h
    case zero =>
      cases n
      case zero => rfl
      case succ n => cases h
    case succ m IH =>
      cases n
      case zero => rfl
      case succ n =>
        let h' := Nat.le_of_succ_le_succ h
        dsimp [List.ofFun]; rw [IH (fun n => f (.succ n)) _ h']

  theorem List.ofFun.ofPushLCtx
    (xs : List α) (heq : xs.length = n) (lctx : Nat → α) :
    List.ofFun (pushLCtxs xs lctx) n = xs :=
    match xs, n with
    | .nil, n => by
      dsimp at heq; rw [← heq]; rfl
    | .cons x xs, _ => by
      dsimp at heq; rw [← heq];
      dsimp [List.ofFun]; rw [pushLCtxs.cons_zero]; apply congrArg
      rw [pushLCtxs.cons_succ_Fn]
      exact List.ofFun.ofPushLCtx xs rfl lctx

  def HList.ofFun {tyf : Nat → α} {β : α → Sort _} (f : ∀ n, β (tyf n)) (n : Nat) :
    HList β (List.ofFun tyf n) :=
    match n with
    | 0 => .nil
    | .succ n' => .cons (f 0) (ofFun (fun n => f (.succ n)) n')

  theorem HList.ofFun.zero {tyf : Nat → α} {β : α → Sort _} (f : ∀ n, β (tyf n)) :
    HList.ofFun f 0 = .nil := rfl

  theorem HList.ofFun.succ {tyf : Nat → α} {β : α → Sort _} (f : ∀ n, β (tyf n)) (n : Nat) :
    HList.ofFun f (.succ n) = .cons (f 0) (ofFun (fun n => f (.succ n)) n) := rfl

  theorem HList.ofFun.ofPushLCtxDep
    {lctxty : α → Sort u} {tys : List α} (heq : tys.length = n)
    (xs : HList lctxty tys) {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) :
    HEq (HList.ofFun (pushLCtxsDep xs lctx) n) xs :=
    match xs, n with
    | .nil, n => by
      dsimp at heq; rw [← heq]; rfl
    | .cons (ty:=ty) (tys:=tys) x xs, _ => by
      dsimp at heq; rw [← heq]
      rw [HList.ofFun.succ];
      congr
      case e_3.h => dsimp; rw [pushLCtxs.cons_zero]
      case e_4.h => dsimp; rw [pushLCtxs.cons_succ_Fn]; apply List.ofFun.ofPushLCtx; rfl
      case e_5 => apply pushLCtxsDep.cons_zero
      case e_6 =>
        apply HEq.trans _ (ofPushLCtxDep rfl xs lctx)
        congr
        case e_2.h => apply pushLCtxs.cons_succ_Fn
        case e_4 => apply pushLCtxsDep.cons_succ_Fn

  theorem HList.ofFun_getD_eq_some
    {tyf : Nat → α} {β : α → Sort _} (f : ∀ n, β (tyf n)) (n m : Nat)
    (h : n > m) {ty : α} (default : β ty) :
    HEq ((HList.ofFun f n).getD default m) (f m) := by
    revert tyf n; induction m <;> intros tyf f n h
    case zero =>
      cases n
      case zero => cases h
      case succ n => rfl
    case succ m IH =>
      cases n
      case zero => cases h
      case succ n =>
        let h' := Nat.le_of_succ_le_succ h
        dsimp [ofFun]; apply (IH (fun n => f (.succ n)) _ h')

  theorem HList.ofFun_getD_eq_none
    {tyf : Nat → α} {β : α → Sort _} (f : ∀ n, β (tyf n)) (n m : Nat)
    (h : n ≤ m) {ty : α} (default : β ty) :
    HEq ((HList.ofFun f n).getD default m) default := by
    revert tyf n; induction m <;> intros tyf f n h
    case zero =>
      cases n
      case zero => rfl
      case succ n => cases h
    case succ m IH =>
      cases n
      case zero => rfl
      case succ n =>
        let h' := Nat.le_of_succ_le_succ h
        dsimp [ofFun]; apply (IH (fun n => f (.succ n)) _ h')

end push


section pushs_pops

  theorem push_pop_eq (lctx : Nat → α) :
    pushLCtx (lctx 0) (fun n => lctx (.succ n)) = lctx := by
    apply funext
    intro n; cases n <;> rfl
  
  theorem pushs_pops_eq (lctx : Nat → α) :
    pushLCtxs (List.ofFun lctx lvl) (fun n => lctx (n + lvl)) = lctx := by
    apply funext; intro n; dsimp [pushLCtxs, List.getD]
    rw [List.ofFun_length]
    match h : Nat.blt n lvl with
    | true =>
      rw [List.ofFun_get?_eq_some]; rfl
      dsimp [Nat.blt] at h;
      exact Nat.le_of_ble_eq_true h
    | false =>
      rw [Nat.sub_add_cancel]
      dsimp [Nat.blt] at h;
      let h' := Nat.lt_of_ble_eq_false h
      exact Nat.le_of_succ_le_succ h'

  theorem pushDep_popDep_eq
    {lctxty : α → Sort u} {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) :
    HEq (pushLCtxDep (lctx 0) (fun n => lctx (.succ n))) lctx := by
    apply HEq.funext;
    intro n; cases n <;> rfl

  theorem pushsDep_popsDep_eq
    {lctxty : α → Sort u} {rty : Nat → α} (lctx : ∀ n, lctxty (rty n)) :
    HEq (pushLCtxsDep (HList.ofFun lctx lvl) (fun n => lctx (n + lvl))) lctx := by
    apply HEq.funext; intro n; dsimp [pushLCtxs, List.getD]
    rw [List.ofFun_length]
    match h : Nat.blt n lvl with
    | true =>
      dsimp;
      apply HList.ofFun_getD_eq_some;
      dsimp [Nat.blt] at h;
      exact Nat.le_of_ble_eq_true h
    | false =>
      rw [Nat.sub_add_cancel]
      dsimp [Nat.blt] at h;
      let h' := Nat.lt_of_ble_eq_false h
      exact Nat.le_of_succ_le_succ h'

end pushs_pops


section add_nat
  
  @[reducible] def addAt (lvl pos : Nat) := mapAt pos (fun x => x + lvl)

  @[reducible] def succAt := addAt 1

  theorem addAt.succ_zero (lvl pos : Nat) :
    addAt lvl (.succ pos) 0 = 0 := rfl
  
  theorem addAt.succ_succ (lvl pos : Nat) (n : Nat) :
    addAt lvl (.succ pos) (.succ n) = .succ (addAt lvl pos n) := by
    dsimp [addAt]; rw [mapAt.succ_succ]

  def addAt.succ_l (lvl pos : Nat) (n : Nat) :
    addAt (.succ lvl) pos n = succAt pos (addAt lvl pos n) := by
    dsimp [addAt, Nat.add_succ]
    rw [mapAt.comp pos Nat.succ (fun x => x + lvl) n]
  
  def addAt.succ_r (lvl pos : Nat) (n : Nat) :
    addAt (.succ lvl) pos n = addAt lvl pos (succAt pos n) := by
    dsimp [addAt];
    have heq : (fun x => x + Nat.succ lvl) = (fun x => (Nat.succ x) + lvl) := by
      apply funext; intros x; rw [Nat.succ_add]; rfl
    rw [heq]; rw [mapAt.comp pos (fun x => x + lvl) Nat.succ n]
  
  def addAt.zero (pos : Nat) : addAt 0 pos = id := by
    apply funext; intro n;
    dsimp [addAt];
    rw [mapAt_id_eq_id']; rfl

  def add.one (pos : Nat) : addAt 1 pos = succAt pos:= rfl

end add_nat


section generic

  theorem restoreAt.succ_pushLCtx {α} (restore : (Nat → α) → (Nat → α))
    (x : α) (pos : Nat) (lctx : Nat → α) (n : Nat) :
    restoreAt (.succ pos) restore (pushLCtx x lctx) n = pushLCtx x (restoreAt pos restore lctx) n :=
    match pos, n with
    | 0,       0        => rfl
    | 0,       .succ _  => rfl
    | .succ _, 0        => rfl
    | .succ _, .succ _ => restoreAt.succ_succ _ _ _ _

  theorem restoreAt.succ_pushLCtx_Fn {α} (restore : (Nat → α) → (Nat → α))
    (x : α) (pos : Nat) (lctx : Nat → α) :
    restoreAt (.succ pos) restore (pushLCtx x lctx) = pushLCtx x (restoreAt pos restore lctx) :=
    funext (fun n => restoreAt.succ_pushLCtx restore x pos lctx n)

  theorem restoreAtDep.succ_pushLCtxDep {α} {lctxty : α → Sort u}
    (restore : (Nat → α) → (Nat → α))
    (restoreDep : ∀ {rty : Nat → α}, (∀ n, lctxty (rty n)) → ∀ n, lctxty ((restore rty) n))
    {rty : Nat → α} {xty : α} (x : lctxty xty) (pos : Nat)
    (lctx : ∀ n, lctxty (rty n)) (n : Nat) :
    HEq (restoreAtDep (.succ pos) restoreDep (pushLCtxDep x lctx) n) (pushLCtxDep x (restoreAtDep pos restoreDep lctx) n) :=
    match pos, n with
    | 0,          0        => HEq.rfl
    | 0,          .succ _  => HEq.rfl
    | .succ _,    0        => HEq.rfl
    | .succ pos', .succ n' => by
      apply HEq.trans (restoreAtDep.succ_succ (Nat.succ pos') restoreDep (pushLCtxDep x lctx) n')
      rw [pushLCtxDep.succ]; rw [pushLCtxDep.succ_Fn]

  theorem restoreAtDep.succ_pushLCtxDep_Fn {α} {lctxty : α → Sort u}
    (restore : (Nat → α) → (Nat → α))
    (restoreDep : ∀ {rty : Nat → α}, (∀ n, lctxty (rty n)) → ∀ n, lctxty ((restore rty) n))
    {rty : Nat → α} {xty : α} (x : lctxty xty) (pos : Nat)
    (lctx : ∀ n, lctxty (rty n)) :
    HEq (restoreAtDep (.succ pos) restoreDep (pushLCtxDep x lctx)) (pushLCtxDep x (restoreAtDep pos restoreDep lctx)) :=
    HEq.funext _ _ (fun n => restoreAtDep.succ_pushLCtxDep restore restoreDep x pos lctx n)

end generic

section genericInst

  theorem covPair.ofPushPop (x : α) :
    covPair Nat.succ (pushLCtx x) := fun _ _ => rfl

  theorem covPairDep.ofPushDepPopDep
    {lctxty : α → Sort u} {xty : α} (x : lctxty xty) :
    covPairDep lctxty Nat.succ (pushLCtx xty) (pushLCtxDep x) :=
    And.intro (covPair.ofPushPop xty) (fun {_} _ _ => HEq.rfl)

  theorem covPair.ofPushsPops
    (lvl : Nat) (xs : List α) (heq : xs.length = lvl) :
    covPair (fun x => x + lvl) (pushLCtxs xs) := by
    revert xs heq; induction lvl <;> intros xs heq lctx n
    case zero =>
      dsimp [pushLCtxs]; cases xs;
      case nil => rfl
      case cons _ _ => cases heq
    case succ lvl IH =>
      dsimp [pushLCtxs]; cases xs;
      case nil => cases heq
      case cons x xs =>
        simp at heq
        rw [← IH xs heq lctx n]
        dsimp [pushLCtxs, Nat.blt, Nat.ble, Nat.add_succ];
        rw [Nat.succ_sub_succ]; rfl

  theorem covPairDep.ofPushsDepPopsDep
    {lctxty : α → Sort u} (lvl : Nat) {tys : List α}
    (xs : HList lctxty tys) (heq : tys.length = lvl) :
    covPairDep lctxty (fun x => x + lvl) (pushLCtxs tys) (pushLCtxsDep xs) :=
    And.intro (covPair.ofPushsPops lvl tys heq) (fun {rty} lctx n => by
      dsimp [pushLCtxsDep, pushLCtxs]; revert tys lctxty n;
      induction lvl <;> intros lctxty tys xs heq lctx n
      case zero =>
        cases xs;
        case nil => rfl
        case cons _ _ => cases heq
      case succ lvl IH =>
        cases xs;
        case nil => cases heq
        case cons ty tys x xs =>
          simp at heq
          apply HEq.trans _ (IH xs heq lctx n)
          dsimp [Nat.blt, Nat.ble, Nat.add_succ]
          rw [Nat.succ_sub_succ]; rfl)

end genericInst