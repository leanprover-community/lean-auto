import Lean
import Auto.Parser.NDFA
open Lean

-- POSIX ERE internal representation
-- **TODO**: Parser for POSIX ERE
namespace Auto.Regex

private def sort : List Nat → List Nat := 
  have : DecidableRel Nat.le := fun (x y : Nat) => inferInstanceAs (Decidable (x <= y))
  List.mergeSort Nat.le

-- Character class
namespace CC

private def alls    := String.mk ((List.range 128).map Char.ofNat)
private def uppers  := "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
private def lowers  := "abcdefghijklmnopqrstuvwxyz"
private def alphas  := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
private def digits  := "0123456789"
private def alnums  := alphas ++ digits
private def xdigits := "0123456789ABCDEFabcdef"
private def puncts  := ".,!?:…"
private def blanks  := " \t"
private def spaces  := " \t\n\r\x0c\x0b"
private def cntrls  := String.mk ((List.range 32).map Char.ofNat)
private def graphs  := String.mk (alls.toList.filter (fun x => !" \t\n\r\x0c\x0b".toList.contains x))
private def prints  := String.mk (alls.toList.filter (fun x => !"\t\n\r\x0c\x0b".toList.contains x))

inductive Ty where
  | all
  | upper
  | lower
  | alpha
  | digit
  | alnum
  | xdigit
  | punct
  | blank
  | space
  | cntrl
  | graph
  | print
deriving BEq, Hashable, Inhabited

def Ty.toString : Ty → String
| .all   => alls
| .upper => uppers
| .lower => lowers
| .alpha => alphas
| .digit => digits
| .alnum => alnums
| .xdigit => xdigits
| .punct => puncts
| .blank => blanks
| .space => spaces
| .cntrl => cntrls
| .graph => graphs
| .print => prints

instance : ToString Ty where
  toString := Ty.toString

end CC

local instance : Hashable Char where
  hash c := hash c.val

inductive EREBracket where
  | cc      : CC.Ty → EREBracket
  -- Match any character contained in the string
  | ofStr   : String → EREBracket
  -- Taking union
  | comp    : Array EREBracket → EREBracket
  -- Takes complement in ascii
  | neg     : EREBracket → EREBracket
deriving BEq, Hashable, Inhabited

-- **TODO**: Why does this need `partial`?
partial def EREBracket.toHashSet : EREBracket → HashSet Char
  | .cc cty      => HashSet.empty.insertMany (toString cty).toList
  | .ofStr s     => HashSet.empty.insertMany s.toList
  | .neg b       =>
    let hb := b.toHashSet
    let alls := (List.range 128).map Char.ofNat
    HashSet.empty.insertMany (alls.filter (fun x => !hb.contains x))
  | .comp ⟨bl⟩    => go bl
where
  go : List EREBracket → HashSet Char
    | [] => HashSet.empty
    | b :: bl => (go bl).insertMany (toHashSet b)

def EREBracket.toString (e : EREBracket) := String.mk e.toHashSet.toList

instance : ToString EREBracket where
  toString := EREBracket.toString

inductive ERE where
  | bracket : EREBracket → ERE
  -- Beginning of string
  | startp  : ERE
  -- End of string
  -- Do not use this in any lexer! It makes no sense
  --   to talk about the "end of string" in a lexer.
  | endp    : ERE
  | star    : ERE → ERE
  -- Repeat exactly `n` times
  | repN    : ERE → (n : Nat) → ERE
  -- Repeat at most `n` times
  | repGe   : ERE → (n : Nat) → ERE
  -- Repeat at least `n` times
  | repLe   : ERE → (n : Nat) → ERE
  -- Repeat at least `n` times and at most `m` times
  | repGeLe : ERE → (n : Nat) → (m : Nat) → ERE
  | comp    : Array ERE → ERE
  | plus     : Array ERE → ERE
deriving BEq, Hashable, Inhabited

-- Match any character in the string
def ERE.ofStr (s : String) := ERE.bracket (.ofStr s)

partial def ERE.brackets : ERE → Array EREBracket
| .bracket b     => #[b]
| .startp        => #[]
| .endp          => #[]
| .star e        => e.brackets
| .repN e _      => e.brackets
| .repGe e _     => e.brackets
| .repLe e _     => e.brackets
| .repGeLe e _ _ => e.brackets
| .comp es       => (es.map ERE.brackets).concatMap id
| .plus es       => (es.map ERE.brackets).concatMap id

partial def ERE.normalizeBrackets : ERE → ERE
| .bracket b     => .bracket (.ofStr (toString b))
| .startp        => .startp
| .endp          => .endp
| .star e        => .star e.normalizeBrackets
| .repN e n      => .repN e.normalizeBrackets n
| .repGe e n     => .repGe e.normalizeBrackets n
| .repLe e n     => .repLe e.normalizeBrackets n
| .repGeLe e n m => .repGeLe e.normalizeBrackets n m
| .comp es       => .comp (es.map normalizeBrackets)
| .plus es       => .plus (es.map normalizeBrackets)

section

  variable (σ : Type) [Hashable σ] [BEq σ] [ToString σ]

  -- Given an `ERE`, group characters that `behaves the same`,
  --   according to all the `bracket`s in this `ERE`
  structure CharGrouping where
    ngroup  : Nat
    -- All relevant characters
    all     : HashSet σ
    -- Map from character to its corresponding group
    charMap : HashMap σ Nat
    -- A character is in `all` iff it's in `charMap`.
    -- Group number takes value in `0, 1, ..., ngroups - 1`
    -- For the intermediate `NFA` generated in `ERE.toADFA`,
    --   the alphabet of the `NFA` will be `0, 1, ..., ngroups + 1`,
    --   where `ngroups` represents beginning of string, and
    --   `ngroups + 1` represents end of string.
  deriving Inhabited

  -- Annotated DFA, the `lexer table`
  structure ADFA where
    -- As stated before, `dfa.tr.size` represents the
    --  `malformed input` state. Moreover (also stated before),
    --   if the transition map of state `i` does not include
    --   an entry for character `c`, then the transition from
    --   `i` to `c` ends in `malformed input` state
    dfa : DFA Nat
    -- As stated before, for the intermediate `NFA` generated
    --   in `ERE.toADFA`, `cg.ngroups` represents beginning
    --   of string, and `cg.ngroups + 1` represents end of string.
    --   Refer to `ERE.toADFA`.
    cg  : CharGrouping σ
  
  variable {σ : Type} [Hashable σ] [BEq σ] [ToString σ]
  
  def CharGrouping.wf : CharGrouping σ → Bool :=
    fun ⟨ngroup, all, charMap⟩ =>
      let img := charMap.fold (fun hs _ n => hs.insert n) HashSet.empty
      let surj := (sort img.toList) == List.range ngroup
      let allInCharMap := all.all (fun c => charMap.contains c)
      let sizeEq := all.size == charMap.size
      surj && allInCharMap && sizeEq
  
  def CharGrouping.groups : CharGrouping σ → Array (HashSet σ) :=
    fun ⟨ngroup, _, charMap⟩ => Id.run <| do
      let mut arr : Array (HashSet σ) := 
        Array.mk ((List.range ngroup).map (fun _ => HashSet.empty))
      for (c, idx) in charMap do
        arr := arr.modify idx (fun hs => hs.insert c)
      return arr

  def CharGrouping.toString : CharGrouping σ → String :=
    fun cg@⟨ngroup, all, _⟩ =>
      let groups := cg.groups.mapIdx (
        fun idx c =>
          s!"{idx.val} : {ToString.toString c.toList}"
      )
      let all := "CharGrouping ⦗⦗" ::
                 s!"Number of groups := {ngroup}" ::
                 s!"All relevant characters := {ToString.toString all.toList}" ::
                 groups.data
      String.intercalate "\n  " all ++ "\n⦘⦘"

  instance : ToString (CharGrouping σ) where
    toString := CharGrouping.toString

  def ADFA.toString : ADFA σ → String :=
    fun ⟨d, cg⟩ =>
      let dsnatS (s : Nat) (sn : _ × Nat) := s!"  ({s}, {sn.fst} → {sn.snd})"
      let dtr := d.tr.mapIdx (fun idx c => c.toArray.map (fun el => dsnatS idx el))
      let dtr := dtr.concatMap id
      let cggroups := cg.groups.mapIdx (
        fun idx c =>
          s!"  {idx.val} : {ToString.toString c.toList}"
      )
      let all := "ADFA ⦗⦗" ::
                 s!"Accept states := {d.accepts.toList}" ::
                 s!"Size (Malformed-input state) = {d.tr.size}" ::
                 s!"Number of groups := {cg.ngroup}" ::
                 s!"All relevant characters := {ToString.toString cg.all.toList}" ::
                 s!"Group representing beginning of string := {cg.ngroup}" ::
                 s!"Group representing end of string := {cg.ngroup + 1}" ::
                 "(GroupIdx, Group members):" ::
                 cggroups.data ++
                 s!"(State, GroupIdx → State'):" ::
                 dtr.data
      String.intercalate "\n  " all ++ "\n⦘⦘"
  
  instance : ToString (ADFA σ) where
    toString := ADFA.toString

end

def CharGrouping.toStringForChar : CharGrouping Char → String :=
  fun cg@⟨ngroup, all, _⟩ =>
    let groups := cg.groups.mapIdx (
      fun idx c =>
        let c := String.mk ((sort (c.toList.map Char.toNat)).map Char.ofNat)
        s!"{idx.val} : {repr c}"
    )
    let alls := String.mk ((sort (all.toList.map Char.toNat)).map Char.ofNat)
    let all := "CharGrouping ⦗⦗" ::
               s!"Number of groups := {ngroup}" ::
               s!"All relevant characters := {repr alls}" ::
               groups.data
    String.intercalate "\n  " all ++ "\n⦘⦘"

instance : ToString (CharGrouping Char) where
  toString := CharGrouping.toStringForChar

def ERE.charGrouping (e : ERE) : CharGrouping Char := Id.run <| do
  let hsets := e.brackets.map EREBracket.toHashSet
  let mut all := hsets.foldl (fun hs nhs => hs.insertMany nhs) HashSet.empty
  let mut charMap := all.fold (fun hs c => hs.insert c 0) HashMap.empty
  -- Current number of groups
  let mut curidx := 1
  for hset in hsets do
    let mut reloc : HashMap Nat Nat := HashMap.empty
    for c in hset do
      let cidx := charMap.find! c
      match reloc.find? cidx with
      | .some r => charMap := charMap.insert c r
      | .none => reloc := reloc.insert cidx curidx;
                 charMap := charMap.insert c curidx;
                 curidx := curidx + 1
  let mut ridx := 0
  let mut reloc : HashMap Nat Nat := HashMap.empty
  for (_, i) in charMap.toList do
    match reloc.find? i with
    | .some _ => continue
    | .none   => reloc := reloc.insert i ridx; ridx := ridx + 1
  charMap := HashMap.ofList (charMap.toList.map (fun (c, i) => (c, reloc.find! i)))
  return CharGrouping.mk ridx all charMap

private partial def ERE.toNFAAux (cg : CharGrouping Char) : ERE → (NFA Nat)
| .bracket b =>
  let bs := toString b
  let states := bs.foldl (fun hs c => hs.insert (cg.charMap.find! c)) HashSet.empty
  NFA.ofSymbAdd states.toArray
| .startp        => NFA.ofSymb (cg.ngroup)
| .endp          => NFA.ofSymb (cg.ngroup + 1)
| .star e        => NFA.star (e.toNFAAux cg)
| .repN e n      => NFA.repeatN (e.toNFAAux cg) n
| .repGe e n     => NFA.repeatAtLeast (e.toNFAAux cg) n
| .repLe e n     => NFA.repeatAtMost (e.toNFAAux cg) n
| .repGeLe e n m => NFA.repeatBounded (e.toNFAAux cg) n m
| .comp es       => NFA.multiComp (es.map (fun e => e.toNFAAux cg))
| .plus es       => NFA.multiPlus (es.map (fun e => e.toNFAAux cg))

def ADFA.toStringForChar : ADFA Char → String :=
  fun ⟨d, cg⟩ =>
    let dsnatS (s : Nat) (sn : _ × Nat) := s!"  ({s}, {sn.fst} → {sn.snd})"
    let dtr := d.tr.mapIdx (fun idx c => c.toArray.map (fun el => dsnatS idx el))
    let dtr := dtr.concatMap id
    let cggroups := cg.groups.mapIdx (
      fun idx c =>
        let c := String.mk ((sort (c.toList.map Char.toNat)).map Char.ofNat)
        s!"  {idx.val} : {repr c}"
    )
    let cgalls := String.mk ((sort (cg.all.toList.map Char.toNat)).map Char.ofNat)
    let all := "ADFA ⦗⦗" ::
               s!"Accept states := {d.accepts.toList}" ::
               s!"Size (Malformed-input state) = {d.tr.size}" ::
               s!"Number of groups := {cg.ngroup}" ::
               s!"All relevant characters := {repr cgalls}" ::
               s!"Group representing beginning of string := {cg.ngroup}" ::
               s!"Group representing end of string := {cg.ngroup + 1}" ::
               "(GroupIdx, Group members):" ::
               cggroups.data ++
               s!"(State, GroupIdx → State'):" ::
               dtr.data
    String.intercalate "\n  " all ++ "\n⦘⦘"

instance : ToString (ADFA Char) where
  toString := ADFA.toStringForChar

def ERE.toADFA (e : ERE) : ADFA Char :=
  let cg := e.charGrouping
  -- Prepend `.repLe .startp 1`, append `.preLe .endp 1`. Later,
  --   before parsing strings, first translate the string (list of char)
  --   into list of groups, then prepend `dfa.ngroups` and append
  --   `dfa.ngroups + 1` to the string
  let nfa := (ERE.comp #[.repLe .startp 1, e, .repLe .endp 1]).toNFAAux cg
  let dfa := DFA.ofNFA nfa
  ⟨dfa, cg⟩

/-

#eval IO.println (ERE.charGrouping (.comp ((
  #[.ofStr "abce", .ofStr "abgh"]).map ERE.bracket)))

#eval IO.println <| ToString.toString (ERE.toADFA
  (.comp #[.plus #[.ofStr "hd", .ofStr "f"], .ofStr "fg#", .bracket (.cc .alpha)]))

-/

end Auto.Regex