-- Computational NFA and DFA
import Lean
import Mathlib.Data.List.Sort
open Lean

namespace Auto

private def sort : List Nat → List Nat := 
  have : DecidableRel Nat.le := fun (x y : Nat) => inferInstanceAs (Decidable (x <= y))
  List.mergeSort Nat.le

section NFA

  -- Alphabet of NFA
  variable (σ : Type) [BEq σ] [Hashable σ]

  instance : BEq (Unit ⊕ σ) where
    beq : Unit ⊕ σ → Unit ⊕ σ → Bool
    | .inl _, .inl _ => true
    | .inr a, .inr b => BEq.beq a b
    | _, _           => false

  instance : Hashable (Unit ⊕ σ) where
    hash : Unit ⊕ σ → UInt64
    | .inl _ => Hashable.hash (0, 0)
    | .inr a => Hashable.hash (1, hash a)

  -- The state of a `n : NFA` is a natual number
  -- The number of states is `n.size`
  -- The set of all possible states is `{0,1,...,n.size}`,
  --   where `0` is the initial state and `n.size` is the accept state
  -- `n` itself represents the transition function
  --   of the `NFA`, where `Unit` is the `ε` transition.
  --   We assume that the accept state does not have any
  --   outward transitions, so it's not recorded in `n`.
  -- So, by definition, the accept state has no outcoming edges.
  -- However, the initial state might have incoming edges
  -- Note that NFA over the character alphabet would be `NFA UInt32`,
  --   this is because `Char` is not `Hashable` in Lean (?), and
  --   the internal representation of `Char` in Lean is `UInt32`.
  abbrev NFA := Array (HashMap (Unit ⊕ σ) (Array Nat))

  variable {σ : Type} [BEq σ] [Hashable σ]

  section Run

    variable [ToString σ]

    def NFA.toString (n : NFA σ) : String :=
      let us2s (x : Unit ⊕ σ) :=
        match x with
        | .inl _ => "ε"
        | .inr s => ToString.toString s
      let snatS (s : Nat) (sn : _ × Array Nat) := s!"({s}, {us2s sn.fst} ↦ {sn.snd.toList})"
      let tr := n.mapIdx (fun idx c =>
        c.toArray.map (fun el => snatS idx el))
      let tr := tr.concatMap id
      let all := "NFA ⦗⦗" :: s!"Accept state := {n.size}" :: tr.data
      String.intercalate "\n  " all ++ "\n⦘⦘"
  
    instance : ToString (NFA σ) where
      toString := NFA.toString
  
    private def NFA.nextStatesOfState (r : NFA σ) (s : Nat) (c : Unit ⊕ σ) : Array Nat :=
      if h₁ : s > r.size then
        panic! s!"NFA.nextStates :: State {s} is not valid for {r}"
      else if h₂ : s = r.size then
        -- Accept state have no outcoming edges
        #[]
      else
        let hmap := r[s]'(
          by simp [Nat.not_gt_eq] at h₁;
             have h₃ : _ := Nat.eq_or_lt_of_le h₁
             have h₄ : (s = Array.size r) = False := eq_false h₂
             simp [h₄] at h₃; simp [h₃]
        )
        match hmap.find? c with
        | .some arr => arr
        | .none     => #[]
    
    -- Why this does not need `partial`?
    def NFA.εClosureOfStates (r : NFA σ) (ss : HashSet Nat) := Id.run <| do
      let mut front := ss.toArray
      let mut cur := 0
      let mut ret := ss
      while front.size > 0 do
        cur := front.back
        front := front.pop
        let curNexts := NFA.nextStatesOfState r cur (.inl .unit)
        for n in curNexts do
          if !ret.contains n then
            front := front.push n
            ret := ret.insert n
      return ret

    def NFA.move (r : NFA σ) (ss : HashSet Nat) (c : σ) :=
      let sss := ss.toArray.map (fun s => NFA.nextStatesOfState r s (.inr c))
      sss.foldl (fun hs s => hs.insertMany s) HashSet.empty

    -- Valid moves from a set of states `ss`, ignoring `ε` transitions
    -- Returns a hashmap from symbol to HashSet of states
    def NFA.moves [ToString σ] (r : NFA σ) (ss : HashSet Nat) : HashMap σ (HashSet Nat) :=
      Id.run <| do
        let mut ret : HashMap σ (HashSet Nat) := HashMap.empty
        for i in ss do
          if i > r.size then
            panic! s!"NFA.moves :: {i} from state set {ss.toList} is not a valid state of {r}"
          -- Accept state has no outward transition
          if i == r.size then
            continue
          if h : i < r.size then
            let hmap := r[i]'(h)
            for (c, dests) in hmap.toList do
              match c with
              -- Ignore `ε` transitions
              | .inl .unit => continue
              | .inr c =>
                if let some d := ret.find? c then
                  ret := ret.insert c (d.insertMany dests)
                else
                  ret := ret.insert c (HashSet.empty.insertMany dests)
        return ret
  
    -- Move, then compute ε-closure
    def NFA.moveε (r : NFA σ) (ss : HashSet Nat) (c : σ) : HashSet Nat :=
      r.εClosureOfStates (r.move ss c)

    def NFA.moveεMany (r : NFA σ) (ss : HashSet Nat) (cs : Array σ) :=
      cs.foldl (fun ss' c => r.moveε ss' c) ss

    def NFA.run (r : NFA σ) (cs : Array σ) :=
      r.moveεMany (r.εClosureOfStates (HashSet.empty.insert 0)) cs
  
  end Run

  -- Criterion : The destination of all transitions should be ≤ n.size
  def NFA.wf (n : NFA σ) : Bool :=
    n.all (fun hmap => hmap.toList.all (fun (_, arr) => arr.all (· <= n.size)))

  -- Delete invalid transitions and turn the NFA into a well-formed one
  def NFA.normalize (n : NFA σ) : NFA σ :=
    let size := n.size
    let normEntry (x : _ × Array Nat) :=
      (x.fst, (HashSet.empty.insertMany (x.snd.filter (· <= size))).toArray)
    n.map (fun hs => HashMap.ofList (hs.toList.map normEntry))

  -- Whether the NFA's initial state has incoming edges
  def NFA.hasEdgeToInit (n : NFA σ) : Bool :=
    n.any (fun hmap => hmap.toList.any (fun (_, arr) => arr.contains 0))

  private def NFA.relocateEntry (x : α × Array Nat) (off : Nat) :=
    (x.fst, x.snd.map (· + off))

  private def NFA.relocateHMap (x : HashMap (Unit ⊕ σ) (Array Nat)) (off : Nat) :=
    HashMap.ofList (x.toList.map (relocateEntry · off))

  private def NFA.addEdges (x : HashMap (Unit ⊕ σ) (Array Nat)) (e : (Unit ⊕ σ) × Array Nat) :=
      x.insert e.fst (match x.find? e.fst with | some arr => arr ++ e.snd | none => e.snd)

  -- Does not accept any string
  def NFA.zero : NFA σ := #[HashMap.empty]

  -- Only accepts empty string
  def NFA.epsilon : NFA σ :=
    #[HashMap.empty.insert (.inl .unit) #[1]]

  -- Accepts a character
  def NFA.char (c : Char) : NFA UInt32 :=
    #[HashMap.empty.insert (.inr c.val) #[1]]

  -- Produce an NFA whose language is the union of `m`'s and `n`'s
  def NFA.plus (m n : NFA σ) : NFA σ :=
    -- `0` is the new initial state
    let off_m := 1
    let off_n := m.size + 2
    -- `acc'` is the new accept state
    let acc' := m.size + n.size + 3
    let initTrans : HashMap (Unit ⊕ σ) (Array Nat) :=
      HashMap.empty.insert (Sum.inl .unit) #[off_m, off_n]
    -- Move the states of `m` by `off_m`
    let new_m := m.map (relocateHMap · off_m)
    let new_m := new_m.push (HashMap.empty.insert (.inl .unit) #[acc'])
    -- Move the states of `n` by `off_n`
    let new_n := n.map (relocateHMap · off_n)
    let new_n := new_n.push (HashMap.empty.insert (.inl .unit) #[acc'])
    #[initTrans] ++ new_m ++ new_n

  def NFA.multiPlus (as : Array (NFA σ)) :=
    match h : as.size with
    | 0 => NFA.zero
    | 1 => as[0]'(by simp[h])
    | _ =>
      let (acc', offs) : Nat × Array Nat :=
        as.foldl (fun (cur, acc) (arr : NFA σ) => (cur + arr.size + 1, acc.push cur)) (1, #[])
      let initTrans : HashMap (Unit ⊕ σ) (Array Nat) :=
        HashMap.empty.insert (Sum.inl .unit) offs
      let arrs := (as.zip offs).map (fun ((a, off) : NFA σ × Nat) =>
          let new_a := a.map (relocateHMap · off)
          new_a.push (HashMap.empty.insert (.inl .unit) #[acc'])
        )
      (#[#[initTrans]] ++ arrs).concatMap id

  def NFA.comp (m n : NFA σ) : NFA σ :=
    -- Connect to `n`
    let new_m := m.mapIdx (fun idx hmap =>
      if idx == m.size then
        addEdges hmap (.inl .unit, #[m.size])
      else hmap
    )
    -- Move the states of `n` by `n.size`
    let new_n := n.map (relocateHMap · m.size)
    new_m ++ new_n

  def NFA.star (m : NFA σ) : NFA σ :=
    -- The new accept state
    let acc' := m.size + 2
    -- The new location of the original accept state of `m`
    -- let macc' := m.size + 1
    let initTrans : HashMap (Unit ⊕ σ) (Array Nat) :=
      HashMap.empty.insert (Sum.inl .unit) #[1, acc']
    -- Move the states of `m` by `1`
    let new_m := m.map (relocateHMap · 1)
    let new_m := new_m.push (HashMap.empty.insert (.inl .unit) #[1, acc'])
    #[initTrans] ++ new_m

  -- Extra functionality
  private def NFA.multiCompAux : List (NFA σ) → NFA σ
  | .nil => NFA.epsilon
  | .cons a .nil => a
  | a :: as => NFA.comp a (NFA.multiCompAux as)

  def NFA.multiComp (a : Array (NFA σ)) := NFA.multiCompAux a.data

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
          #[HashMap.empty.insert (.inl .unit) #[1]] ++ r.map (relocateHMap · 1)
        else
          r
      let acc' := n * r.size
      let arrs := (Array.mk (List.range n)).map (fun i =>
          -- Relocate
          let new_r := r.map (relocateHMap · (i * r.size))
          -- Add an edge from initial state to new accept state
          new_r.modify 0 (fun hm => NFA.addEdges hm (.inl .unit, #[acc']))
        )
      arrs.concatMap id

  def NFA.repeatBounded (r : NFA σ) (n : Nat) (m : Nat) :=
  if n > m then
    NFA.epsilon
  else
    NFA.comp (r.repeatN n) (r.repeatAtMost (m - n))

  -- Accepts all characters in an array of characters
  def NFA.chars (cs : Array Char) : NFA UInt32 :=
    #[HashMap.ofList (cs.map (fun c => (.inr c.val,#[1]))).data]

  -- An `NFA UInt32` that accepts exactly a string
  def NFA.charOfString (s : String) : NFA UInt32 :=
    (Array.mk s.data).mapIdx (fun idx c => HashMap.empty.insert (.inr c.val) #[idx + 1])

  /-

  def test₁ : NFA String := #[
      HashMap.ofList [(.inr "a", #[5]), (.inr "b", #[1, 0])],
      HashMap.ofList [(.inl .unit, #[1]), (.inr "c", #[2,4]), (.inr "a", #[6,1,2])]
    ]
  
  def test₂ : NFA String := test₁.normalize

  #eval IO.println test₁
  #eval test₁.wf
  #eval IO.println test₂
  #eval test₂.wf
  #eval IO.println (NFA.epsilon (σ:=String))
  #eval IO.println (test₂.comp test₂)
  #eval IO.println (test₂.plus test₂)
  #eval IO.println test₂.star
  #eval IO.println (NFA.chars #['a', 'c', 'd', '🍉'])
  #eval IO.println (NFA.charOfString "acd🍉")
  #eval IO.println (NFA.repeatAtMost (NFA.charOfString "ab") 2)
  #eval IO.println (NFA.repeatAtMost test₂ 2)
  #eval IO.println (NFA.repeatN (NFA.char 'a') 5)
  #eval IO.println (NFA.charOfString "aaaaa")

  def test₃ := NFA.multiPlus (#["a", "dfw", "e4"].map NFA.charOfString)

  #eval IO.println test₃
  #eval test₃.wf
  #eval (test₃.move (HashSet.empty.insert 0) 'a'.val).toList
  #eval (test₃.εClosureOfStates (HashSet.empty.insert 0)).toList
  #eval (test₃.move (HashSet.empty.insertMany [7,3,1,0]) 'a'.val).toList

  -/

end NFA

section DFA
  
  -- Alphabet of DFA
  variable (σ : Type) [BEq σ] [Hashable σ]

  structure DFA where
    -- Array of accept states
    accepts : HashSet Nat
    -- Transition function
    -- `0` is the initial statet
    -- `{0, 1, ⋯, tr.size}` are the set of allowed states, where
    --   `tr.size` is the special `malformed input` state
    -- `accepts` should be a subset of `{0, 1, ⋯, tr.size - 1}`
    -- If the transition map of state `i` does not include
    --   an entry for character `c`, then the transition from
    --   `i` to `c` ends in `malformed input` state
    tr      : Array (HashMap σ Nat)
  
  variable {σ : Type} [BEq σ] [Hashable σ] [ToString σ]

  def DFA.toString (d : DFA σ) : String :=
    let snatS (s : Nat) (sn : σ × Nat) := s!"({s}, {sn.fst} → {sn.snd})"
    let tr := d.tr.mapIdx (fun idx c => c.toArray.map (fun el => snatS idx el))
    let tr := tr.concatMap id
    let all := "DFA ⦗⦗" ::
               s!"Accept states := {d.accepts.toList}" ::
               s!"Size/Malformed-input state = {d.tr.size}" ::
               tr.data
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
        by simp [Nat.not_gt_eq] at h₁;
           have h₃ : _ := Nat.eq_or_lt_of_le h₁
           have h₄ : (s = Array.size _) = False := eq_false h₂
           simp [h₄] at h₃; simp [h₃]
      )
      match hmap.find? c with
      | .some s => s
      -- `malformed input`
      | .none   => d.tr.size

  def DFA.ofNFA (n : NFA σ) : DFA σ := Id.run <| do
    if !n.wf then
      panic! s!"DFA.ofNFA :: {n} is not well-formed"
    -- Array of states
    let mut dstates : Array (List Nat) := #[sort (n.εClosureOfStates (HashSet.empty.insert 0)).toList]
    -- Map from state to idx of state
    let mut idxmap : HashMap (List Nat) Nat :=
      HashMap.empty.insert dstates[0] 0
    -- `Unit` represents the `malformed input` state
    let mut tr : Array (HashMap σ (Nat ⊕ Unit)) := #[HashMap.empty]
    -- Next state to process
    let mut cur := 0
    while h : cur < dstates.size do
      let st := dstates[cur]
      let moves := n.moves (HashSet.empty.insertMany st)
      for (c, st) in moves do
        -- If `st` is empty, then the move ends in `malformed input` state
        if st.size == 0 then
          tr := tr.modify cur (fun hmap => hmap.insert c (.inr .unit))
          continue
        -- `ε`-closure of the move
        let εst := sort (n.εClosureOfStates st).toList
        if !idxmap.contains εst then
          dstates := dstates.push εst
          idxmap := idxmap.insert εst idxmap.size
          tr := tr.push HashMap.empty
        -- Now `idxmap` contains `εst`
        let idx := idxmap.find! εst
        tr := tr.modify cur (fun hmap => hmap.insert c (.inl idx))
      cur := cur + 1
    let rettr := tr.map (
      fun hmap => HashMap.ofList (hmap.toList.map (
        fun (s, nu) =>
          match nu with
          | .inl n => (s, n)
          | .inr .unit => (s, tr.size)
      ))
    )
    let accepts := dstates.mapIdx (fun idx l => if l.contains n.size then some idx.val else none)
    let accepts := accepts.foldl (fun hs o => if let some x := o then hs.insert x else hs) HashSet.empty
    return DFA.mk accepts rettr

  def test₄ : DFA String := ⟨HashSet.empty.insert 3, #[
    HashMap.ofList [("a", 5), ("b", 0)],
    HashMap.ofList [("q", 1), ("c", 4), ("a", 2)]
  ]⟩

  /-

  def test₅ : NFA UInt32 := NFA.repeatAtMost (NFA.charOfString "ab") 2
  def test₆ : NFA UInt32 := NFA.repeatAtLeast (NFA.charOfString "ab") 200

  #eval (do IO.println test₂; IO.println (DFA.ofNFA test₂))
  #eval (do IO.println test₃; IO.println (DFA.ofNFA test₃))
  #eval (do IO.println test₅; IO.println (DFA.ofNFA test₅))
  #eval (do IO.println test₆; IO.println (DFA.ofNFA test₆))

  -/

end DFA

end Auto
