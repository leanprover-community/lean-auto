-- Computational NFA and DFA
module

public import Lean
public import Auto.Lib.ListExtra

public section

open Lean

namespace Auto

private def sort : List Nat → List Nat :=
  have : DecidableRel Nat.le := fun (x y : Nat) => inferInstanceAs (Decidable (x <= y))
  List.mergeSort Nat.le

section NFA

  -- Alphabet of NFA
  variable (σ : Type) [BEq σ] [Hashable σ]

  local instance : BEq (Unit ⊕ σ) where
    beq : Unit ⊕ σ → Unit ⊕ σ → Bool
    | .inl _, .inl _ => true
    | .inr a, .inr b => BEq.beq a b
    | _, _           => false

  local instance : Hashable (Unit ⊕ σ) where
    hash : Unit ⊕ σ → UInt64
    | .inl _ => Hashable.hash (0, 0)
    | .inr a => Hashable.hash (1, hash a)

  /--
    The state of a `n : NFA` is a natual number
    The number of states is `n.tr.size`
    The set of all possible states is `{0,1,...,n.tr.size}`,
      where `0` is the initial state and `n.size` is the accept state
    `n.tr` represents the transition function
      of the `NFA`, where `Unit` is the `ε` transition.
      We assume that the accept state does not have any
      outward transitions, so it's not recorded in `n`.
    So, by definition, the accept state has no outcoming edges.
    However, the initial state might have incoming edges
  -/
  structure NFA where
    tr    : Array (Std.HashMap (Unit ⊕ σ) (Array Nat))
    -- Each state (including the accept state) is associated
    --   with an array of attributes. So the length of `attrs`
    --   should be `tr.size + 1`
    attrs : Array (Std.HashSet String)
  deriving Inhabited

  variable {σ : Type} [BEq σ] [Hashable σ]

  section Run

    variable [ToString σ]

    def NFA.toString (n : NFA σ) : String :=
      let us2s (x : Unit ⊕ σ) :=
        match x with
        | .inl _ => "ε"
        | .inr s => ToString.toString s
      let snatS (s : Nat) (sn : _ × Array Nat) := s!"({s}, {us2s sn.fst} ↦ {sn.snd.toList})"
      let tr := n.tr.mapIdx (fun idx c =>
        c.toArray.map (fun el => snatS idx el))
      let tr := tr.flatMap id
      let attrs := n.attrs.mapIdx (fun idx attrs => s!"{idx} : {attrs.toList}")
      let all := "NFA ⦗⦗" :: s!"Accept state := {n.tr.size}" :: tr.toList ++ attrs.toList
      String.intercalate "\n  " all ++ "\n⦘⦘"

    instance : ToString (NFA σ) where
      toString := NFA.toString

    private def NFA.nextStatesOfState (r : NFA σ) (s : Nat) (c : Unit ⊕ σ) : Array Nat :=
      if h₁ : s > r.tr.size then
        panic! s!"NFA.nextStates :: State {s} is not valid for {r}"
      else if h₂ : s = r.tr.size then
        -- Accept state have no outcoming edges
        #[]
      else
        let hmap := r.tr[s]'(
          by simp only [Nat.not_gt_eq] at h₁;
             have h₃ : _ := Nat.eq_or_lt_of_le h₁
             have h₄ : (s = Array.size r.tr) = False := eq_false h₂
             simp [h₄] at h₃; simp [h₃]
        )
        match hmap.get? c with
        | .some arr => arr
        | .none     => #[]

    -- Why this does not need `partial`?
    def NFA.εClosureOfStates (r : NFA σ) (ss : Std.HashSet Nat) := Id.run <| do
      let mut front := ss.toArray
      let mut cur := 0
      let mut ret := ss
      while front.size > 0 do
        cur := front.back!
        front := front.pop
        let curNexts := NFA.nextStatesOfState r cur (.inl .unit)
        for n in curNexts do
          if !ret.contains n then
            front := front.push n
            ret := ret.insert n
      return ret

    def NFA.move (r : NFA σ) (ss : Std.HashSet Nat) (c : σ) :=
      let sss := ss.toArray.map (fun s => NFA.nextStatesOfState r s (.inr c))
      sss.foldl (fun hs s => hs.insertMany s) Std.HashSet.emptyWithCapacity

    -- Valid moves from a set of states `ss`, ignoring `ε` transitions
    -- Returns a hashmap from symbol to HashSet of states
    def NFA.moves [ToString σ] (r : NFA σ) (ss : Std.HashSet Nat) : Std.HashMap σ (Std.HashSet Nat) :=
      Id.run <| do
        let mut ret : Std.HashMap σ (Std.HashSet Nat) := {}
        for i in ss do
          if i > r.tr.size then
            panic! s!"NFA.moves :: {i} from state set {ss.toList} is not a valid state of {r}"
          -- Accept state has no outward transition
          if i == r.tr.size then
            continue
          if h : i < r.tr.size then
            let hmap := r.tr[i]'(h)
            for (c, dests) in hmap.toList do
              match c with
              -- Ignore `ε` transitions
              | .inl .unit => continue
              | .inr c =>
                if let some d := ret.get? c then
                  ret := ret.insert c (d.insertMany dests)
                else
                  ret := ret.insert c (Std.HashSet.emptyWithCapacity.insertMany dests)
        return ret

    -- Move, then compute ε-closure
    def NFA.moveε (r : NFA σ) (ss : Std.HashSet Nat) (c : σ) : Std.HashSet Nat :=
      r.εClosureOfStates (r.move ss c)

    def NFA.moveεMany (r : NFA σ) (ss : Std.HashSet Nat) (cs : Array σ) :=
      cs.foldl (fun ss' c => r.moveε ss' c) ss

    def NFA.run (r : NFA σ) (cs : Array σ) :=
      r.moveεMany (r.εClosureOfStates (Std.HashSet.emptyWithCapacity.insert 0)) cs

  end Run

  /-- Criterion : The destination of all transitions should be ≤ n.size -/
  def NFA.wf (n : NFA σ) : Bool :=
    n.tr.size >= 1
    && n.tr.all (fun hmap => hmap.toList.all (fun (_, arr) => arr.all (· <= n.tr.size)))
    && n.attrs.size == n.tr.size + 1

  /-- Delete invalid transitions and turn the NFA into a well-formed one -/
  def NFA.normalize (n : NFA σ) : NFA σ :=
    let size := n.tr.size
    let normEntry (x : _ × Array Nat) :=
      (x.fst, (Std.HashSet.emptyWithCapacity.insertMany (x.snd.filter (· <= size))).toArray)
    let tr' := n.tr.map (fun hs => Std.HashMap.ofList (hs.toList.map normEntry))
    let attrs' := n.attrs[0:size+1].toArray
    let attrs' := attrs'.append ⟨(List.range (size + 1 - attrs'.size)).map (fun _ => Std.HashSet.emptyWithCapacity)⟩
    NFA.mk tr' attrs'

  /-- Whether the NFA's initial state has incoming edges -/
  def NFA.hasEdgeToInit (n : NFA σ) : Bool :=
    n.tr.any (fun hmap => hmap.toList.any (fun (_, arr) => arr.contains 0))

  private def NFA.relocateEntry (x : α × Array Nat) (off : Nat) :=
    (x.fst, x.snd.map (· + off))

  private def NFA.relocateHMap (x : Std.HashMap (Unit ⊕ σ) (Array Nat)) (off : Nat) :=
    Std.HashMap.ofList (x.toList.map (relocateEntry · off))

  private def NFA.addEdgesToHMap (x : Std.HashMap (Unit ⊕ σ) (Array Nat)) (e : (Unit ⊕ σ) × Array Nat) :=
      x.insert e.fst (match x.get? e.fst with | some arr => arr ++ e.snd | none => e.snd)

  /-- Add attribute to a specific state -/
  def NFA.addAttrToState (n : NFA σ) (s : Nat) (attr : String) :=
    if s >= n.attrs.size then
      panic!"NFA.addAttrToState :: Invalid state {s} for {n}"
    else
      let new_attrs := n.attrs.modify s (fun hs => hs.insert attr)
      NFA.mk n.tr new_attrs

  /-- Add attribute to accept state -/
  def NFA.addAttr (n : NFA σ) (attr : String) :=
    if n.attrs.size = 0 then
      panic!"NFA.addAttr :: Invalid {n}"
    else
      let new_attrs := n.attrs.modify (n.attrs.size - 1) (fun hs => hs.insert attr)
      NFA.mk n.tr new_attrs

  /-- Does not accept any string -/
  def NFA.zero : NFA σ := NFA.mk #[Std.HashMap.emptyWithCapacity] #[.emptyWithCapacity, .emptyWithCapacity]

  /-- Only accepts empty string -/
  def NFA.epsilon : NFA σ :=
    NFA.mk #[Std.HashMap.emptyWithCapacity.insert (.inl .unit) #[1]] #[.emptyWithCapacity, .emptyWithCapacity]

  /-- Accepts a character -/
  def NFA.ofSymb (c : σ) : NFA σ :=
    NFA.mk #[Std.HashMap.emptyWithCapacity.insert (.inr c) #[1]] #[.emptyWithCapacity, .emptyWithCapacity]

  /-- Produce an NFA whose language is the union of `m`'s and `n`'s -/
  def NFA.plus (m n : NFA σ) : NFA σ :=
    -- `0` is the new initial state
    let off_m := 1
    let off_n := m.tr.size + 2
    -- `acc'` is the new accept state
    let acc' := m.tr.size + n.tr.size + 3
    let initTrans : Std.HashMap (Unit ⊕ σ) (Array Nat) :=
      Std.HashMap.emptyWithCapacity.insert (Sum.inl .unit) #[off_m, off_n]
    -- Move the states of `m` by `off_m`
    let new_mtr := m.tr.map (relocateHMap · off_m)
    let new_mtr := new_mtr.push (Std.HashMap.emptyWithCapacity.insert (.inl .unit) #[acc'])
    -- Move the states of `n` by `off_n`
    let new_ntr := n.tr.map (relocateHMap · off_n)
    let new_ntr := new_ntr.push (Std.HashMap.emptyWithCapacity.insert (.inl .unit) #[acc'])
    let new_tr := #[initTrans] ++ new_mtr ++ new_ntr
    let new_attrs := #[Std.HashSet.emptyWithCapacity] ++ m.attrs ++ n.attrs ++ #[Std.HashSet.emptyWithCapacity]
    NFA.mk new_tr new_attrs

  def NFA.multiPlus (as : Array (NFA σ)) :=
    match h : as.size with
    | 0 => NFA.zero
    | 1 => as[0]'(by simp[h])
    | _ =>
      let (acc', offs) : Nat × Array Nat :=
        as.foldl (fun (cur, acc) (arr : NFA σ) => (cur + arr.tr.size + 1, acc.push cur)) (1, #[])
      let initTrans : Std.HashMap (Unit ⊕ σ) (Array Nat) :=
        Std.HashMap.emptyWithCapacity.insert (Sum.inl .unit) offs
      let trs := (as.zip offs).map (fun ((a, off) : NFA σ × Nat) =>
          let new_a := a.tr.map (relocateHMap · off)
          new_a.push (Std.HashMap.emptyWithCapacity.insert (.inl .unit) #[acc'])
        )
      let new_tr := (#[#[initTrans]] ++ trs).flatMap id
      let new_attrs := #[Std.HashSet.emptyWithCapacity] ++
                       (as.map (fun (⟨_, attrs⟩ : NFA σ) => attrs)).flatMap id ++
                       #[Std.HashSet.emptyWithCapacity]
      NFA.mk new_tr new_attrs

  def NFA.comp (m n : NFA σ) : NFA σ :=
    -- Connect to `n`
    let new_mtr := m.tr.mapIdx (fun idx hmap =>
      if idx == m.tr.size then
        addEdgesToHMap hmap (.inl .unit, #[m.tr.size])
      else hmap
    )
    -- Move the states of `n` by `n.size`
    let new_ntr := n.tr.map (relocateHMap · m.tr.size)
    let new_tr := new_mtr ++ new_ntr
    if h₁ : m.attrs.size = 0 then
      panic!"NFA.comp :: Invalid {m}"
    else if h₂ : n.attrs.size = 0 then
      panic!"NFA.comp :: Invalid {n}"
    else
      let new_attrs :=
        m.attrs[:m.attrs.size - 1].toArray ++
        #[(m.attrs[m.attrs.size - 1]'(by
            apply Nat.sub_lt
            apply Nat.zero_lt_of_ne_zero
            simp [h₁]; simp
            )).insertMany
          (n.attrs[0]'(by
            apply Nat.zero_lt_of_ne_zero
            simp [h₂]
            ))] ++
        n.attrs[1:].toArray
      NFA.mk new_tr new_attrs

  def NFA.star (m : NFA σ) : NFA σ :=
    -- The new accept state
    let acc' := m.tr.size + 2
    -- The new location of the original accept state of `m`
    -- let macc' := m.size + 1
    let initTrans : Std.HashMap (Unit ⊕ σ) (Array Nat) :=
      Std.HashMap.emptyWithCapacity.insert (Sum.inl .unit) #[1, acc']
    -- Move the states of `m` by `1`
    let new_mtr := m.tr.map (relocateHMap · 1)
    let new_mtr := new_mtr.push (Std.HashMap.emptyWithCapacity.insert (.inl .unit) #[1, acc'])
    let new_tr := #[initTrans] ++ new_mtr
    let new_attrs := #[.emptyWithCapacity] ++ m.attrs ++ #[.emptyWithCapacity]
    NFA.mk new_tr new_attrs

  /-- Extra functionality -/
  private def NFA.multiCompAux : List (NFA σ) → NFA σ
  | .nil => NFA.epsilon
  | .cons a .nil => a
  | a :: as => NFA.comp a (NFA.multiCompAux as)

  def NFA.multiComp (a : Array (NFA σ)) := NFA.multiCompAux a.toList

  def NFA.repeatN (r : NFA σ) (n : Nat) := NFA.multiComp ⟨(List.range n).map (fun _ => r)⟩

  def NFA.repeatAtLeast (r : NFA σ) (n : Nat) := NFA.comp (r.repeatN n) (.star r)

  def NFA.repeatAtMost (r : NFA σ) (n : Nat) : NFA σ :=
    if n == 0 then
      NFA.epsilon
    else
      let r :=
        if r.hasEdgeToInit then
          -- Add a new state as the initial state so that the
          --   new initial state has no incoming edges
          let new_tr := #[Std.HashMap.emptyWithCapacity.insert (.inl .unit) #[1]] ++ r.tr.map (relocateHMap · 1)
          let new_attrs := #[.emptyWithCapacity] ++ r.attrs
          NFA.mk new_tr new_attrs
        else
          r
      let acc' := n * r.tr.size
      let new_trs := (Array.mk (List.range n)).map (fun i =>
          -- Relocate
          let new_r := r.tr.map (relocateHMap · (i * r.tr.size))
          -- Add an edge from initial state to new accept state
          new_r.modify 0 (fun hm => NFA.addEdgesToHMap hm (.inl .unit, #[acc']))
        )
      let new_tr := new_trs.flatMap id
      let new_attrs : Array (Std.HashSet String) :=
        ((Array.mk (List.range (n - 1))).map (fun _ => r.attrs[:r.tr.size].toArray)).flatMap id ++
        r.attrs
      NFA.mk new_tr new_attrs

  def NFA.repeatBounded (r : NFA σ) (n : Nat) (m : Nat) :=
  if n > m then
    NFA.epsilon
  else
    NFA.comp (r.repeatN n) (r.repeatAtMost (m - n))

  /-- Accepts all characters in an array of characters -/
  def NFA.ofSymbPlus (cs : Array σ) : NFA σ :=
    NFA.mk #[Std.HashMap.ofList (cs.map (fun c => (.inr c,#[1]))).toList] #[.emptyWithCapacity, .emptyWithCapacity]

  /-- An `NFA UInt32` that accepts exactly a string -/
  def NFA.ofSymbComp (s : Array σ) : NFA σ :=
    let tr := (Array.mk s.toList).mapIdx (fun idx c => Std.HashMap.emptyWithCapacity.insert (.inr c) #[idx + 1])
    let attrs := Array.mk ((List.range (s.size + 1)).map (fun _ => .emptyWithCapacity))
    NFA.mk tr attrs

  /-

  local instance : Hashable Char where
    hash c := hash c.val

  def test₁ : NFA String := ⟨#[
      Std.HashMap.ofList [(.inr "a", #[5]), (.inr "b", #[1, 0])],
      Std.HashMap.ofList [(.inl .unit, #[1]), (.inr "c", #[2, 4]), (.inr "a", #[6,1,2])]
    ], #[]⟩

  def test₂ : NFA String := test₁.normalize

  #eval IO.println test₁
  #eval test₁.wf
  #eval IO.println test₂
  #eval test₂.wf
  #eval IO.println (NFA.epsilon (σ:=String))
  #eval IO.println (test₂.comp test₂)
  #eval IO.println (test₂.plus test₂)
  #eval IO.println test₂.star
  #eval IO.println (NFA.ofSymbPlus #['a', 'c', 'd', '🍉'])
  #eval IO.println (NFA.ofSymbComp ⟨"acd🍉".toList⟩)
  #eval IO.println (NFA.repeatAtMost (NFA.ofSymbComp ⟨"ab".toList⟩) 2)
  #eval IO.println (NFA.repeatAtMost test₂ 2)
  #eval IO.println (NFA.repeatN (NFA.ofSymb 'a') 5)
  #eval IO.println (NFA.ofSymbComp ⟨"aaaaa".toList⟩)

  def test₃ := NFA.multiPlus (#["a", "dfw", "e4"].map (fun s => NFA.ofSymbComp ⟨s.toList⟩))

  #eval IO.println test₃
  #eval test₃.wf
  #eval (test₃.move (Std.HashSet.emptyWithCapacity.insert 0) 'a').toList
  #eval (test₃.εClosureOfStates (Std.HashSet.emptyWithCapacity.insert 0)).toList
  #eval (test₃.move (Std.HashSet.emptyWithCapacity.insertMany [7,3,1,0]) 'a').toList

  -/

end NFA

section DFA

  -- Alphabet of DFA
  variable (σ : Type) [BEq σ] [Hashable σ]

  structure DFA where
    -- Array of accept states
    accepts : Std.HashSet Nat
    -- Transition function
    -- `0` is the initial statet
    -- `{0, 1, ⋯, tr.size}` are the set of allowed states, where
    --   `tr.size` is the special `malformed input` state
    -- `accepts` should be a subset of `{0, 1, ⋯, tr.size - 1}`
    -- If the transition map of state `i` does not include
    --   an entry for character `c`, then the transition from
    --   `i` to `c` ends in `malformed input` state
    tr      : Array (Std.HashMap σ Nat)
    -- Each state (except for the `malformed input` state)
    --   is associated with an array of attributes.
    -- So, we should have `attrs.size == tr.size`
    attrs   : Array (Std.HashSet String)
  deriving Inhabited

  variable {σ : Type} [BEq σ] [Hashable σ] [ToString σ]

  def DFA.toString (d : DFA σ) : String :=
    let snatS (s : Nat) (sn : σ × Nat) := s!"({s}, {sn.fst} → {sn.snd})"
    let tr := d.tr.mapIdx (fun idx c => c.toArray.map (fun el => snatS idx el))
    let tr := tr.flatMap id
    let attrs := d.attrs.mapIdx (fun idx attrs => s!"{idx} : {attrs.toList}")
    let all := "DFA ⦗⦗" ::
               s!"Accept states := {d.accepts.toList}" ::
               s!"Size (Malformed-input state) = {d.tr.size}" ::
               tr.toList ++ attrs.toList
    String.intercalate "\n  " all ++ "\n⦘⦘"

  instance : ToString (DFA σ) where
    toString := DFA.toString

  def DFA.move (d : DFA σ) (s : Nat) (c : σ) :=
    if h₁ : s > d.tr.size then
      panic! s!"DFA.move :: State {s} is not valid for {d}"
    -- Starting at `malformed input` state
    else if h₂ : s = d.tr.size then
      -- Ends in `malformed input` state
      d.tr.size
    else
      let hmap := d.tr[s]'(
        by simp only [Nat.not_gt_eq] at h₁;
           have h₃ : _ := Nat.eq_or_lt_of_le h₁
           have h₄ : (s = Array.size _) = False := eq_false h₂
           simp [h₄] at h₃; simp [h₃]
      )
      match hmap.get? c with
      | .some s => s
      -- `malformed input`
      | .none   => d.tr.size

  def DFA.ofNFA (n : NFA σ) : DFA σ := Id.run <| do
    if !n.wf then
      panic! s!"DFA.ofNFA :: {n} is not well-formed"
    -- Array of states
    let mut dstates : Array (List Nat) := #[sort (n.εClosureOfStates (Std.HashSet.emptyWithCapacity.insert 0)).toList]
    -- Map from state to idx of state
    let mut idxmap : Std.HashMap (List Nat) Nat :=
      Std.HashMap.emptyWithCapacity.insert dstates[0]! 0
    -- `Unit` represents the `malformed input` state
    let mut tr : Array (Std.HashMap σ (Nat ⊕ Unit)) := #[{}]
    -- Next state to process
    let mut cur := 0
    while h : cur < dstates.size do
      let st := dstates[cur]
      let moves := n.moves (Std.HashSet.emptyWithCapacity.insertMany st)
      for (c, st) in moves.toList do
        -- If `st` is empty, then the move ends in `malformed input` state
        if st.size == 0 then
          tr := tr.modify cur (fun hmap => hmap.insert c (.inr .unit))
          continue
        -- `ε`-closure of the move
        let εst := sort (n.εClosureOfStates st).toList
        if !idxmap.contains εst then
          dstates := dstates.push εst
          idxmap := idxmap.insert εst idxmap.size
          tr := tr.push {}
        -- Now `idxmap` contains `εst`
        let idx := idxmap.get! εst
        tr := tr.modify cur (fun hmap => hmap.insert c (.inl idx))
      cur := cur + 1
    let rettr := tr.map (
      fun hmap => Std.HashMap.ofList (hmap.toList.map (
        fun (s, nu) =>
          match nu with
          | .inl n => (s, n)
          | .inr .unit => (s, tr.size)
      ))
    )
    let accepts := dstates.mapIdx (fun idx l => if l.contains n.tr.size then some idx else none)
    let accepts := accepts.foldl (fun hs o => if let some x := o then hs.insert x else hs) Std.HashSet.emptyWithCapacity
    let attrs := dstates.map (fun l =>
      (Array.mk l).foldl (fun acc s => if let some x := n.attrs[s]? then acc.insertMany x else acc) Std.HashSet.emptyWithCapacity)
    return DFA.mk accepts rettr attrs

  /-

  def test₄ : DFA String := ⟨Std.HashSet.emptyWithCapacity.insert 3, #[
    Std.HashMap.ofList [("a", 5), ("b", 0)],
    Std.HashMap.ofList [("q", 1), ("c", 4), ("a", 2)]], #[.empty, .empty]⟩

  local instance : Hashable Char where
    hash c := hash c.val

  def test₅ : NFA Char := NFA.repeatAtMost (NFA.ofSymbComp ⟨"ab".toList⟩) 2
  def test₆ : NFA Char := NFA.repeatAtLeast (NFA.ofSymbComp ⟨"ab".toList⟩) 200

  #eval (do IO.println test₂; IO.println (DFA.ofNFA test₂))
  #eval (do IO.println test₃; IO.println (DFA.ofNFA test₃))
  #eval (do IO.println test₅; IO.println (DFA.ofNFA test₅))
  #eval (do IO.println test₆; IO.println (DFA.ofNFA test₆))

  -/

end DFA

end Auto
