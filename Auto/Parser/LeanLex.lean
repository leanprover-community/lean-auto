import Lean
import Auto.Parser.NDFA
open Lean

set_option linter.unusedVariables false

namespace Auto

-- POSIX ERE internal representation
-- **TODO**: Parser for POSIX ERE
namespace Regex

private def sort : List Nat → List Nat :=
  have : DecidableRel Nat.le := fun (x y : Nat) => inferInstanceAs (Decidable (x <= y))
  List.mergeSort Nat.le

-- Character class
namespace CC

private def alls    := String.ofList ((List.range 128).map Char.ofNat)
private def uppers  := "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
private def lowers  := "abcdefghijklmnopqrstuvwxyz"
private def alphas  := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
private def digits  := "0123456789"
private def alnums  := alphas ++ digits
private def xdigits := "0123456789ABCDEFabcdef"
private def puncts  := ".,!?:…"
private def blanks  := " \t"
private def spaces  := " \t\n\r\x0c\x0b"
private def cntrls  := String.ofList ((List.range 32).map Char.ofNat)
private def graphs  := String.ofList (alls.toList.filter (fun x => !" \t\n\r\x0c\x0b".toList.contains x))
private def prints  := String.ofList (alls.toList.filter (fun x => !"\t\n\r\x0c\x0b".toList.contains x))

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

/-- Taking complement of `b` with respect to the set of ascii characters -/
def EREBracket.neg (b : EREBracket) : EREBracket := .minus b (.cc .all)

-- **TODO**: Why does this need `partial`?
partial def EREBracket.toHashSet : EREBracket → Std.HashSet Char
  | .cc cty       => Std.HashSet.emptyWithCapacity.insertMany (toString cty).toList
  | .inStr s      => Std.HashSet.emptyWithCapacity.insertMany s.toList
  | .plus ⟨bl⟩     => go bl
  | .minus b1 b2  =>
    let hb := b2.toHashSet
    let b1s := b1.toHashSet.toList
    Std.HashSet.emptyWithCapacity.insertMany (b1s.filter (fun x => !hb.contains x))
where
  go : List EREBracket → Std.HashSet Char
    | [] => Std.HashSet.emptyWithCapacity
    | b :: bl => (go bl).insertMany (toHashSet b)

def EREBracket.toString (e : EREBracket) := String.ofList e.toHashSet.toList

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
  | epsilon  : ERE
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

/-- Match any character in the string -/
def ERE.inStr (s : String) := ERE.bracket (.inStr s)

/-- Match the given string -/
def ERE.ofStr (s : String) := ERE.comp ⟨s.toList.map (fun c => .inStr (String.ofList [c]))⟩

def ERE.ofCC (c : CC.Ty) := ERE.bracket (.cc c)

/-- Optional, corresponding to `?` -/
def ERE.opt (e : ERE) := e.repLe 1

/-- Nonempty sequence of, corresponding to `+` -/
def ERE.some (e : ERE) := e.repGe 1

partial def ERE.brackets : ERE → Array EREBracket
| .bracket b     => #[b]
| .bracketN b    => #[b]
| .startp        => #[]
| .endp          => #[]
| .epsilon       => #[]
| .star e        => e.brackets
| .repN e _      => e.brackets
| .repGe e _     => e.brackets
| .repLe e _     => e.brackets
| .repGeLe e _ _ => e.brackets
| .comp es       => (es.map ERE.brackets).flatMap id
| .plus es       => (es.map ERE.brackets).flatMap id
| .attr e _      => e.brackets

partial def ERE.normalizeBrackets : ERE → ERE
| .bracket b     => .bracket (.inStr (toString b))
| .bracketN b    => .bracketN (.inStr (toString b))
| .startp        => .startp
| .endp          => .endp
| .epsilon       => .epsilon
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

  /--
    Given an `ERE`, group characters that `behaves the same`,
      according to all the `bracket`s in this `ERE`
  -/
  structure CharGrouping where
    ngroup  : Nat
    -- All relevant characters
    all     : Std.HashSet σ
    -- Map from character to its corresponding group
    charMap : Std.HashMap σ Nat
    -- A character is in `all` iff it's in `charMap`.
    -- Group number takes value in `0, 1, ..., ngroups - 1`
    -- For the intermediate `NFA` generated in `ERE.toADFA`,
    --   the alphabet of the `NFA` will be `0, 1, ..., ngroups + 2`,
    --   where `ngroups` represents beginning of string,
    --   `ngroups + 1` represents end of string, and `ngroups + 2`
    --   is the complement of `all` with respect to the set
    --   of `utf-8` characters
  deriving Inhabited

  /-- Annotated DFA, the `lexer table` -/
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
      let img := charMap.fold (fun hs _ n => hs.insert n) Std.HashSet.emptyWithCapacity
      let surj := (sort img.toList) == List.range ngroup
      let allInCharMap := all.toList.all (fun c => charMap.contains c)
      let sizeEq := all.size == charMap.size
      surj && allInCharMap && sizeEq

  def CharGrouping.groups : CharGrouping σ → Array (Std.HashSet σ) :=
    fun ⟨ngroup, _, charMap⟩ => Id.run <| do
      let mut arr : Array (Std.HashSet σ) :=
        Array.mk ((List.range ngroup).map (fun _ => Std.HashSet.emptyWithCapacity))
      for (c, idx) in charMap.toList do
        arr := arr.modify idx (fun hs => hs.insert c)
      return arr

  def CharGrouping.toStringAux : CharGrouping σ → (symbListToString : Array σ → String) → String :=
    fun cg@⟨ngroup, all, _⟩ symbListToString =>
    let groups := cg.groups.mapIdx (
      fun idx c =>
        s!"{idx} : {symbListToString c.toArray}"
    )
    let all := "CharGrouping ⦗⦗" ::
               s!"Number of groups := {ngroup}" ::
               s!"All relevant characters := {symbListToString all.toArray}" ::
               s!"Group representing beginning of string := {ngroup}" ::
               s!"Group representing end of string := {ngroup + 1}" ::
               s!"Group representing other utf-8 characters := {ngroup + 2}" ::
               groups.toList
    String.intercalate "\n  " all ++ "\n⦘⦘"

  def CharGrouping.toString (cg : CharGrouping σ) : String :=
    CharGrouping.toStringAux cg ToString.toString

  instance : ToString (CharGrouping σ) where
    toString := CharGrouping.toString

  def CharGrouping.getGroup (cg : CharGrouping σ) (c : σ) : Nat :=
    match cg.charMap.get? c with
    | .some g => g
    -- Invalid character
    | .none   => cg.ngroup + 2

  def ADFA.toStringAux : ADFA σ → (symbListToString : Array σ → String) → String :=
    fun ⟨d, cg⟩ symbListToString =>
      let dsnatS (s : Nat) (sn : _ × Nat) := s!"  ({s}, {sn.fst} → {sn.snd})"
      let dtr := d.tr.mapIdx (fun idx c => c.toArray.map (fun el => dsnatS idx el))
      let dtr := dtr.flatMap id
      let attrs := d.attrs.mapIdx (fun idx attrs => s!"  {idx} : {attrs.toList}")
      let cggroups := cg.groups.mapIdx (
        fun idx c =>
          s!"  {idx} : {symbListToString c.toArray}"
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
                 "(GroupIdx, Group members):" :: cggroups.toList ++
                 s!"(State, GroupIdx → State'):" :: dtr.toList ++
                 s!"(State, Attributes)" :: attrs.toList
      String.intercalate "\n  " all ++ "\n⦘⦘"

  def ADFA.toString (a : ADFA σ) : String := ADFA.toStringAux a
    (fun l => ToString.toString l.toList)

  instance : ToString (ADFA σ) where
    toString := ADFA.toString

  def ADFA.getAttrs (a : ADFA σ) (state : Nat) :=
    match a.dfa.attrs[state]? with
    | .some attrs => attrs
    | .none       => panic! s!"ADFA.getAttrs :: {state} is an invalid state for {a}"

end

def CharGrouping.toStringForChar (cg : CharGrouping Char) : String :=
  CharGrouping.toStringAux cg (fun l =>
    let sorted := sort (l.toList.map Char.toNat)
    let str := String.ofList (sorted.map Char.ofNat)
    ToString.toString (repr str))

instance : ToString (CharGrouping Char) where
  toString := CharGrouping.toStringForChar

def ADFA.toStringForChar (a : ADFA Char) : String :=
  ADFA.toStringAux a (fun l =>
    let sorted := sort (l.toList.map Char.toNat)
    let str := String.ofList (sorted.map Char.ofNat)
    ToString.toString (repr str))

instance : ToString (ADFA Char) where
  toString := ADFA.toStringForChar

def ERE.charGrouping (e : ERE) : CharGrouping Char := Id.run <| do
  let hsets := e.brackets.map EREBracket.toHashSet
  let mut all := hsets.foldl (fun hs nhs => hs.insertMany nhs) Std.HashSet.emptyWithCapacity
  let mut charMap := all.fold (fun hs c => hs.insert c 0) Std.HashMap.emptyWithCapacity
  -- Current number of groups
  let mut curidx := 1
  for hset in hsets do
    let mut reloc : Std.HashMap Nat Nat := {}
    for c in hset do
      let cidx := charMap.get! c
      match reloc.get? cidx with
      | .some r => charMap := charMap.insert c r
      | .none => reloc := reloc.insert cidx curidx;
                 charMap := charMap.insert c curidx;
                 curidx := curidx + 1
  let mut ridx := 0
  let mut reloc : Std.HashMap Nat Nat := {}
  for (_, i) in charMap.toList do
    match reloc.get? i with
    | .some _ => continue
    | .none   => reloc := reloc.insert i ridx; ridx := ridx + 1
  charMap := Std.HashMap.ofList (charMap.toList.map (fun (c, i) => (c, reloc.get! i)))
  return CharGrouping.mk ridx all charMap

private partial def ERE.toNFAAux (cg : CharGrouping Char) : ERE → (NFA Nat)
| .bracket b     =>
  let bs := toString b
  let states := bs.foldl (fun hs c => hs.insert (cg.charMap.get! c)) Std.HashSet.emptyWithCapacity
  NFA.ofSymbPlus states.toArray
| .bracketN b    =>
  let bs := toString b
  -- All `utf-8` characters
  let initHs := Std.HashSet.emptyWithCapacity.insertMany ((cg.ngroup + 2) :: List.range cg.ngroup)
  let states := bs.foldl (fun hs c => hs.erase (cg.charMap.get! c)) initHs
  NFA.ofSymbPlus states.toArray
| .startp        => NFA.ofSymb (cg.ngroup)
| .endp          => NFA.ofSymb (cg.ngroup + 1)
| .epsilon       => NFA.epsilon
| .star e        => NFA.star (e.toNFAAux cg)
| .repN e n      => NFA.repeatN (e.toNFAAux cg) n
| .repGe e n     => NFA.repeatAtLeast (e.toNFAAux cg) n
| .repLe e n     => NFA.repeatAtMost (e.toNFAAux cg) n
| .repGeLe e n m => NFA.repeatBounded (e.toNFAAux cg) n m
| .comp es       => NFA.multiComp (es.map (fun e => e.toNFAAux cg))
| .plus es       => NFA.multiPlus (es.map (fun e => e.toNFAAux cg))
| .attr e s      => NFA.addAttr (e.toNFAAux cg) s

def ERE.toADFA (e : ERE) (prependStartP := true) : ADFA Char :=
  let cg := e.charGrouping
  -- Prepend `.star .startp` to the `ERE`. Later, before parsing strings,
  --   first translate the string (list of char) into list of groups,
  --   then prepend `dfa.ngroups` and append `dfa.ngroups + 1` to the
  --   string.
  -- We do not append `.star .endp` because
  --   1. Note that the lexer terminates and returns the
  --      currently matched lexicon if match has already begun
  --      and it finds that the next symbol will cause the DFA to
  --      transition into `malformed input` state.
  --   2. So, if no lexicon ending with `.endp` can be matched,
  --      the lexer simply returns one without `.endp` if there is any.
  --   3. Moreover, if we do append `.star .endp` to the `ERE`,
  --      there will be problem with attributes: appending
  --      `.star .endp` to the `ERE` while appending `dfa.ngroups + 1`
  --      to the input string will make originally attributed states
  --      transition into new (introduced by `.star .endp`) unattributed
  --      states, given that the lexicon matches to the end of string.
  let ere := if prependStartP then ERE.comp #[.star .startp, e] else e
  let nfa := ere.toNFAAux cg
  let dfa := DFA.ofNFA nfa
  ⟨dfa, cg⟩

structure LexConfig where
  short  := false
  strict := false
  -- Initial state of the DFA
  initS  := 0
  -- Prepend the group indicating beginning of string
  -- Set this option to `false` if you're resuming from
  --   a previous incomplete match.
  prependBeginS := true
  -- Append the group indicating end of string
  -- If you want to do an incomplete match and resume later, either
  -- 1. Set `appendEndS` to `false`, or
  -- 2. Set `appendEndS` to `true` but never use `.endp` in
  --    your `ERE` used to generate the `ADFA`
  appendEndS    := true

inductive LexResultTy where
  | complete
  | incomplete
  | malformed
deriving Inhabited, Hashable, BEq

def LexResultTy.toString : LexResultTy → String
| .complete => "LexResultTy.complete"
| .incomplete => "LexResultTy.incomplete"
| .malformed => "LexResultTy.malformed"

instance : ToString LexResultTy where
  toString := LexResultTy.toString

structure LexResult where
  type       : LexResultTy
  -- Matched part
  matched    : Substring.Raw
  -- Whether the appended `end of string` group is matched
  endSMatched : Bool
  state      : Nat
deriving Inhabited, BEq

def LexResult.toString : LexResult → String := fun ⟨ty, matched, em, state⟩ =>
  s!"{ty} (matched := {repr matched.toString}) (endSMatched := {em}) (state := {state})"

instance : ToString LexResult where
  toString := LexResult.toString

/--
  Usage : First use `ERE.toADFA` to generate
    the lexing table in another file `<f>` and use
    `initialize` to store it, then call the following
    function in another file, where the `ADFA` is
    the one initialized in `<f>`.
  Leftmost match, eager (in finding the first matching character) and
    matches at least one character.
    `short = false` : Longest match, default
    `short = true`  : Shortest match
    `strict = false`: Start from the first valid character, default
    `strict = true` : Start from the first character of `s`
  Note that if we can't find the matching first character with
    `strict = false`, we just return `incomplete`
  This function takes an `ADFA` generated by
    `ERE.toADFA (e : ERE)`, a string `s`. It first finds the leftmost
    character in `s` that is a [valid first character of the lexicon]
    (thus the name `eager`). Then, it returns the longest match
    (as a substring) if there is one, and returns `none` otherwise.
  We prepend `s` with the "beginning of string" group
    and append to `s` the "end of string" group
-/
def ERE.ADFALexEagerL (a : ADFA Char) (s : Substring.Raw) (cfg : LexConfig) : LexResult := Id.run <| do
  -- Current position in `s`
  let mut p : String.Pos.Raw := s.startPos
  -- The value of `b` will represent where the match begins
  let mut b : String.Pos.Raw := s.startPos
  -- `es` records the last successful match. The first
  --   `String.Pos` is where the lexicon ends, and the
  --   `Nat` is the state of the `DFA` when the lexicon
  --   ends. We record this state because we need to
  --   extract its attributes if this turns out to be
  --   the longest match.
  let mut es : Option (String.Pos.Raw × Nat) := none
  let beginString : Nat := a.cg.ngroup
  let endString : Nat := a.cg.ngroup + 1
  let mut endReached : Bool := false
  let mut endSMatched : Bool := false
  let mut state : Nat :=
    if cfg.prependBeginS then
      -- Implicitly prepend `s` with "beginning of string"
      a.dfa.move cfg.initS beginString
    else
      cfg.initS
  let sGetGroupFromPos (p : String.Pos.Raw) : Id Nat := (do
    if p == s.stopPos then
      -- Implicitly append `s` with "end of string"
      return endString
    else
      let .some c := String.Pos.Raw.get? s.str p
        | panic! s!"ERE.ADFALex :: Invalid position {p} for string {s.str}"
      return a.cg.getGroup c)
  -- Matched at least one character
  let mut matchStarted : Bool := false
  if cfg.strict then
    -- First character must be a valid match
    let c := String.Pos.Raw.get! s.str p
    let cgp := a.cg.getGroup c
    let state' := a.dfa.move state cgp
    if state' == a.dfa.tr.size then
      return ⟨.malformed, ⟨s.str, p, p⟩, false, state⟩
    b := p; state := state'; matchStarted := true; p := p + c
  while true do
    -- Put `matchStarted` here because we want to match
    --   at least one character
    if matchStarted && a.dfa.accepts.contains state then
      es := .some (p, state)
      if cfg.short then
        break
    if p == s.stopPos then
      if endReached || !cfg.appendEndS then
        break
      else
        -- If end of string is reached, set `endReached` to
        --   `true` and process `endString`
        endReached := true
    let cgp := sGetGroupFromPos p
    let state' := a.dfa.move state cgp
    match matchStarted, state' == a.dfa.tr.size with
    -- If `state'` is `malformed input`, stop matching and do not change `p`
    | true, true   => break
    -- If `state'` is valid, update `state`
    | true, false  =>
      state := state'
      endSMatched := endReached
    -- If the symbol is not valid as the first symbol of a matching
    --   substring, continue searching for valid first symbol
    | false, true  => pure ()
    -- If the symbol is valid as the first symbol, start matching
    | false, false => b := p; state := state'; matchStarted := true
    if !endReached then
      let c := String.Pos.Raw.get! s.str p
      p := p + c
  match es with
  | .some (e, finalstate) =>
    return ⟨.complete, ⟨s.str, b, e⟩, endSMatched, finalstate⟩
  | .none =>
    if state == a.dfa.tr.size || p != s.stopPos then
      ⟨.malformed, ⟨s.str, b, p⟩, endSMatched, state⟩
    else
      ⟨.incomplete, ⟨s.str, b, p⟩, endSMatched, state⟩

/-

#eval IO.println (ERE.charGrouping (.comp ((
  #[.inStr "abce", .inStr "abgh"]).map ERE.bracket)))

def test₁ := ERE.toADFA
  (.comp #[.plus #[.inStr "hd", .inStr "f"], .inStr "fg#", .bracket (.cc .alpha)])

def test₂ := ERE.toADFA
  (.plus #[.attr (.ofStr "abc") "fst", .ofStr "efg"])

def test₃ := ERE.toADFA
  (.comp #[.ofStr "ab", .bracketN (.inStr "pd🍉")])

def test₄ := ERE.toADFA
  (.comp #[.star (.ofCC .all), .inStr "a"])

def test₅ := ERE.toADFA
  (.comp #[.plus #[.inStr "ab", .epsilon], .comp #[.startp, .ofStr "cd"]])

def test₆ := ERE.toADFA
  (.comp #[.comp #[.ofStr "cd", .endp], .plus #[.inStr "ab", .epsilon]])

private def testit (a : ADFA Char) (s : Substring) (short:=false) (strict:=false) : IO Unit := do
  let r := ERE.ADFALexEagerL a s {short:=short, strict:=strict}
  let attrs := a.getAttrs r.state
  IO.println r
  IO.println attrs.toList

#eval IO.println test₁
#eval test₁.dfa.move 2 3
#eval testit test₁ "? f#a ".toSubstring -- "f#a"
#eval testit test₁ "? f".toSubstring -- incomplete
#eval testit test₁ "? f".toSubstring (strict:=true) -- malformed
#eval testit test₁ "f".toSubstring (strict:=true) -- incomplete
#eval testit test₁ "? fl".toSubstring -- malformed
#eval IO.println test₂
#eval testit test₂ " abc ".toSubstring -- "abc", "[fst]"
#eval testit test₂ " abc".toSubstring -- "abc", "[fst]"
#eval IO.println test₃
#eval testit test₃ " ab🍈 ".toSubstring -- "ab🍈"
#eval IO.println test₄
#eval testit test₄ "🍈🍈89*a9abh".toSubstring -- "89*a9a"
#eval testit test₄ "🍈🍈89*a9abh".toSubstring (short:=true) -- "89*a"
#eval IO.println test₅
#eval testit test₅ "cd".toSubstring -- "cd"
#eval testit test₅ "abcd".toSubstring -- "malformed"
#eval IO.println test₆
#eval testit test₆ "cdab".toSubstring -- "malformed"
#eval testit test₆ " cd".toSubstring -- "cd"

-/

end Regex

end Auto
