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
  | inStr   : String → EREBracket
  -- Taking union
  | plus    : Array EREBracket → EREBracket
  -- Takes complement of `b2` with respect to `b1`
  | minus   : (b1 : EREBracket) → (b2 : EREBracket) → EREBracket
deriving BEq, Hashable, Inhabited

-- Taking complement of `b` with respect to the set of ascii characters
def EREBracket.neg (b : EREBracket) : EREBracket := .minus b (.cc .all)

-- **TODO**: Why does this need `partial`?
partial def EREBracket.toHashSet : EREBracket → HashSet Char
  | .cc cty       => HashSet.empty.insertMany (toString cty).toList
  | .inStr s      => HashSet.empty.insertMany s.toList
  | .plus ⟨bl⟩     => go bl
  | .minus b1 b2  =>
    let hb := b2.toHashSet
    let b1s := b1.toHashSet.toList
    HashSet.empty.insertMany (b1s.filter (fun x => !hb.contains x))
where
  go : List EREBracket → HashSet Char
    | [] => HashSet.empty
    | b :: bl => (go bl).insertMany (toHashSet b)

def EREBracket.toString (e : EREBracket) := String.mk e.toHashSet.toList

instance : ToString EREBracket where
  toString := EREBracket.toString

inductive ERE where
  | bracket  : EREBracket → ERE
  -- Complement of bracket with respect to the set of `utf-8` characters
  | bracketN : EREBracket → ERE
  -- Beginning of string
  --   Do not use this in any lexer! In many
  --   cases there are whitespaces between
  --   tokens, so your `startp` will not correctly
  --   match the beginning of the token.
  | startp   : ERE
  -- End of string
  --   Do not use this in any lexer! It makes no sense
  --   to talk about the "end of string" in a lexer.
  | endp     : ERE
  | star     : ERE → ERE
  -- Repeat exactly `n` times
  | repN     : ERE → (n : Nat) → ERE
  -- Repeat at most `n` times
  | repGe    : ERE → (n : Nat) → ERE
  -- Repeat at least `n` times
  | repLe    : ERE → (n : Nat) → ERE
  -- Repeat at least `n` times and at most `m` times
  | repGeLe  : ERE → (n : Nat) → (m : Nat) → ERE
  | comp     : Array ERE → ERE
  | plus     : Array ERE → ERE
  | attr     : ERE → String → ERE
deriving BEq, Hashable, Inhabited

-- Match any character in the string
def ERE.inStr (s : String) := ERE.bracket (.inStr s)

-- Match the given string
def ERE.ofStr (s : String) := ERE.comp ⟨s.toList.map (fun c => .inStr (String.mk [c]))⟩

def ERE.ofCC (c : CC.Ty) := ERE.bracket (.cc c)

-- Optional, corresponding to `?`
def ERE.opt (e : ERE) := e.repLe 1

-- Nonempty sequence of, corresponding to `+`
def ERE.some (e : ERE) := e.repGe 1

partial def ERE.brackets : ERE → Array EREBracket
| .bracket b     => #[b]
| .bracketN b    => #[b]
| .startp        => #[]
| .endp          => #[]
| .star e        => e.brackets
| .repN e _      => e.brackets
| .repGe e _     => e.brackets
| .repLe e _     => e.brackets
| .repGeLe e _ _ => e.brackets
| .comp es       => (es.map ERE.brackets).concatMap id
| .plus es       => (es.map ERE.brackets).concatMap id
| .attr e s      => e.brackets

partial def ERE.normalizeBrackets : ERE → ERE
| .bracket b     => .bracket (.inStr (toString b))
| .bracketN b    => .bracketN (.inStr (toString b))
| .startp        => .startp
| .endp          => .endp
| .star e        => .star e.normalizeBrackets
| .repN e n      => .repN e.normalizeBrackets n
| .repGe e n     => .repGe e.normalizeBrackets n
| .repLe e n     => .repLe e.normalizeBrackets n
| .repGeLe e n m => .repGeLe e.normalizeBrackets n m
| .comp es       => .comp (es.map normalizeBrackets)
| .plus es       => .plus (es.map normalizeBrackets)
| .attr e s      => .attr e.normalizeBrackets s

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
    --   the alphabet of the `NFA` will be `0, 1, ..., ngroups + 2`,
    --   where `ngroups` represents beginning of string,
    --   `ngroups + 1` represents end of string, and `ngroups + 2`
    --   is the complement of `all` with respect to the set
    --   of `utf-8` characters
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
    --   of string, `cg.ngroups + 1` represents end of string,
    --   and `ngroups + 2` is the complement of `all` with
    --   respect to the set of `utf-8` characters
    --   Refer to `ERE.toADFA`, `ERE.ADFALex` and `DFA.run`
    cg  : CharGrouping σ
  deriving Inhabited
  
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

  def CharGrouping.toStringAux : CharGrouping σ → (symbListToString : Array σ → String) → String :=
    fun cg@⟨ngroup, all, _⟩ symbListToString =>
    let groups := cg.groups.mapIdx (
      fun idx c =>
        s!"{idx.val} : {symbListToString c.toArray}"
    )
    let all := "CharGrouping ⦗⦗" ::
               s!"Number of groups := {ngroup}" ::
               s!"All relevant characters := {symbListToString all.toArray}" ::
               s!"Group representing beginning of string := {ngroup}" ::
               s!"Group representing end of string := {ngroup + 1}" ::
               s!"Group representing other utf-8 characters := {ngroup + 2}" ::
               groups.data
    String.intercalate "\n  " all ++ "\n⦘⦘"

  def CharGrouping.toString (cg : CharGrouping σ) : String :=
    CharGrouping.toStringAux cg ToString.toString

  instance : ToString (CharGrouping σ) where
    toString := CharGrouping.toString

  def CharGrouping.getGroup (cg : CharGrouping σ) (c : σ) : Nat :=
    match cg.charMap.find? c with
    | .some g => g
    -- Invalid character
    | .none   => cg.ngroup + 2

  def ADFA.toStringAux : ADFA σ → (symbListToString : Array σ → String) → String :=
    fun ⟨d, cg⟩ symbListToString =>
      let dsnatS (s : Nat) (sn : _ × Nat) := s!"  ({s}, {sn.fst} → {sn.snd})"
      let dtr := d.tr.mapIdx (fun idx c => c.toArray.map (fun el => dsnatS idx el))
      let dtr := dtr.concatMap id
      let attrs := d.attrs.mapIdx (fun idx attrs => s!"  {idx} : {attrs.toList}")
      let cggroups := cg.groups.mapIdx (
        fun idx c =>
          s!"  {idx.val} : {symbListToString c.toArray}"
      )
      let cgalls := symbListToString cg.all.toArray
      let all := "ADFA ⦗⦗" ::
                 s!"Accept states := {d.accepts.toList}" ::
                 s!"Size (Malformed-input state) = {d.tr.size}" ::
                 s!"Number of groups := {cg.ngroup}" ::
                 s!"All relevant characters := {cgalls}" ::
                 s!"Group representing beginning of string := {cg.ngroup}" ::
                 s!"Group representing end of string := {cg.ngroup + 1}" ::
                 s!"Group representing other utf-8 characters := {cg.ngroup + 2}" ::
                 "(GroupIdx, Group members):" :: cggroups.data ++
                 s!"(State, GroupIdx → State'):" :: dtr.data ++
                 s!"(State, Attributes)" :: attrs.data
      String.intercalate "\n  " all ++ "\n⦘⦘"

  def ADFA.toString (a : ADFA σ) : String := ADFA.toStringAux a
    (fun l => ToString.toString l.toList)
  
  instance : ToString (ADFA σ) where
    toString := ADFA.toString

end

def CharGrouping.toStringForChar (cg : CharGrouping Char) : String :=
  CharGrouping.toStringAux cg (fun l => 
    let sorted := sort (l.toList.map Char.toNat)
    let str := String.mk (sorted.map Char.ofNat)
    ToString.toString (repr str))

instance : ToString (CharGrouping Char) where
  toString := CharGrouping.toStringForChar

def ADFA.toStringForChar (a : ADFA Char) : String :=
  ADFA.toStringAux a (fun l => 
    let sorted := sort (l.toList.map Char.toNat)
    let str := String.mk (sorted.map Char.ofNat)
    ToString.toString (repr str))

instance : ToString (ADFA Char) where
  toString := ADFA.toStringForChar

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
| .bracket b     =>
  let bs := toString b
  let states := bs.foldl (fun hs c => hs.insert (cg.charMap.find! c)) HashSet.empty
  NFA.ofSymbPlus states.toArray
| .bracketN b    =>
  let bs := toString b
  -- All `utf-8` characters
  let initHs := HashSet.empty.insertMany ((cg.ngroup + 2) :: List.range cg.ngroup)
  let states := bs.foldl (fun hs c => hs.erase (cg.charMap.find! c)) initHs
  NFA.ofSymbPlus states.toArray
| .startp        => NFA.ofSymb (cg.ngroup)
| .endp          => NFA.ofSymb (cg.ngroup + 1)
| .star e        => NFA.star (e.toNFAAux cg)
| .repN e n      => NFA.repeatN (e.toNFAAux cg) n
| .repGe e n     => NFA.repeatAtLeast (e.toNFAAux cg) n
| .repLe e n     => NFA.repeatAtMost (e.toNFAAux cg) n
| .repGeLe e n m => NFA.repeatBounded (e.toNFAAux cg) n m
| .comp es       => NFA.multiComp (es.map (fun e => e.toNFAAux cg))
| .plus es       => NFA.multiPlus (es.map (fun e => e.toNFAAux cg))
| .attr e s      => NFA.addAttr (e.toNFAAux cg) s

def ERE.toADFA (e : ERE) : ADFA Char :=
  let cg := e.charGrouping
  -- Prepend `.repLe .startp 1`, append `.preLe .endp 1`. Later,
  --   before parsing strings, first translate the string (list of char)
  --   into list of groups, then prepend `dfa.ngroups` and append
  --   `dfa.ngroups + 1` to the string
  -- Note that the state after the `.endp` transition will have no
  --   attributes, hence we'll have to keep the previous state if
  --   we want to get the lexion's corresponding attribute.
  --   However, this is not a problem in lexing since we never
  --   use `.startp` or `.endp` during lexing.
  let nfa := (ERE.comp #[.repLe .startp 1, e, .repLe .endp 1]).toNFAAux cg
  let dfa := DFA.ofNFA nfa
  ⟨dfa, cg⟩

-- Rationale : First use `ERE.toADFA` to generate
--   the lexing table in another file `<f>` and use
--   `initialize` to store it, then call the following
--   function in another file, where the `ADFA` is
--   the one initialized in `<f>`
-- This function takes an `ADFA` generated by
--   `ERE.toADFA`, a string `s`, and outputs the
--   substring which represents the leftmost longest
--   match against `a`.
-- We assume that `.startp` and `.endp` is not used
--   in the `ERE` used to generate `a`.
def ERE.ADFALex (a : ADFA Char) (s : Substring) : Option (Substring × HashSet String) := Id.run <| do
  let mut p : String.Pos := s.startPos
  let mut b : String.Pos := s.startPos
  let mut e : String.Pos := s.startPos
  let mut state : Nat := 0
  let mut matchStart : Bool := false
  while true do
    if p == s.stopPos then
      -- If end of string is reached, stop matching
      e := p
      break
    else
      let .some c := s.str.get? p
        | panic! s!"ERE.ADFALex :: Invalid position {p} for string {s.str}"
      let cgp := a.cg.getGroup c
      let state' := a.dfa.move state cgp
      match matchStart, state' == a.dfa.tr.size with
      -- If `state'` is `malformed input`, stop matching and do not add to `p`
      | true, true   => e := p; break
      -- If `state'` is valid, update `state`
      | true, false  => state := state'
      -- If the symbol is not valid as the first symbol of a matching
      --   substring, continue searching for valid first symbol
      | false, true  => pure ()
      -- If the symbol is valid as the first symbol, start matching
      | false, false => b := p; state := state'; matchStart := true
      p := p + c
  if matchStart && a.dfa.accepts.contains state then
    if state >= a.dfa.attrs.size then
      panic!"ERE.ADFALex :: {state} is invalid for {a.dfa}"
    else
      return .some (⟨s.str, b, e⟩, a.dfa.attrs[state]!)
  else
    return .none

/-

#eval IO.println (ERE.charGrouping (.comp ((
  #[.inStr "abce", .inStr "abgh"]).map ERE.bracket)))

def test₁ := ERE.toADFA
  (.comp #[.plus #[.inStr "hd", .inStr "f"], .inStr "fg#", .bracket (.cc .alpha)])

#eval IO.println test₁

#eval test₁.dfa.move 2 3

#eval (ERE.ADFALex test₁ "? f#a ".toSubstring).map (fun x => x.1.stopPos)

def test₂ := ERE.toADFA (.plus #[.attr (.ofStr "abc") "fst", .ofStr "efg"])

#eval IO.println test₂
 
#eval (ERE.ADFALex test₂ " efg ".toSubstring).map (fun x => x.1.startPos)

def test₃ := ERE.toADFA (.comp #[.ofStr "ab", .bracketN (.inStr "pd🍉")])

#eval IO.println test₃

#eval (ERE.ADFALex test₃ " ab🍈 ".toSubstring).map (fun x => x.1.startPos)

-/

end Auto.Regex