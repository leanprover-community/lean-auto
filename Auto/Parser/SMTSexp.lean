import Lean
import Auto.Parser.LexInit
open Lean


namespace Auto

open Lexer

namespace Parser.SMTSexp

inductive LexVal
  | lparen
  | rparen
  -- n + dec * 10^(-ndec)
  | nat (n : Nat)
  -- n / m
  | rat (n : Nat) (m : Nat)
  | str (s : String)
  | symb (s : String)
  | kw (s : String)
  | comment (s : String)
deriving Inhabited, BEq, Hashable

def LexVal.toString : LexVal → String
| .lparen  => "("
| .rparen  => ")"
| .nat n   => s!"{n}"
| .rat n m =>
  let pow := s!"{m}".length - 1
  if m != Nat.pow 10 pow then
    panic!"LexVal :: .rat {n} {m} is not yet supported, because {m} is not a power of 10"
  else
    let nint := n / m
    let nfrac := n % m
    let nfracs := s!"{nfrac}"
    let nfracs :=
      String.mk ((List.range (pow - nfracs.length)).map (fun _ => '0')) ++
      nfracs
    s!"{nint}." ++ nfracs
| .str s   => "\"" ++ String.intercalate "\"\"" (s.splitOn "\"") ++ "\""
| .symb s  => s!"|{s}|"
| .kw s    => s!":{s}"
| .comment s => s!";{s}\n"

instance : ToString LexVal where
  toString := LexVal.toString

private def hexDigitToNat (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

def LexVal.ofString (s : String) (attr : String) : LexVal :=
  match attr with
  | "("           => .lparen
  | ")"           => .rparen
  | "numeral"     => .nat s.toNat!
  | "decimal"     =>
    if let [a, b] := s.splitOn "." then
      let a := a.toNat!
      let fracDigits := b.length
      let fracPow := Nat.pow 10 fracDigits
      let b := b.toNat!
      .rat (a * fracPow + b) fracPow
    else
      panic! s!"LexVal.ofString :: {repr s} is not a valid decimal number"
  | "hexadecimal" =>
    let hdigs := s.drop 2
    .nat (hdigs.foldl (fun x c => x * 16 + hexDigitToNat c) 0)
  | "binary" =>
    let bdigs := s.drop 2
    .nat (bdigs.foldl (fun x c => x * 2 + c.toNat - '0'.toNat) 0)
  | "string" =>
    let subs := ((s.drop 1).take (s.length - 2)).splitOn "\"\""
    .str (String.intercalate "\"" subs)
  | "simplesymbol" => .symb s
  | "quotedsymbol" => .symb ((s.drop 1).take (s.length - 2))
  | "keyword"      => .kw (s.drop 1)
  | "comment"      =>
    let rn : Nat := if s.get (s.prev (s.prev s.endPos)) == '\r' then 1 else 0
    .comment ((s.drop 1).take (s.length - 2 - rn))
  | _              => panic! s!"LexVal.ofString :: {repr attr} is not a valid attribute"

inductive Sexp where
  | atom : LexVal → Sexp
  | app  : Array Sexp → Sexp
deriving Inhabited, BEq, Hashable

partial def Sexp.toString : Sexp → String
| .atom l => ToString.toString l
| .app ls => "(" ++ String.intercalate " " (ls.map toString).toList ++ ")"

instance : ToString Sexp where
  toString e := Sexp.toString e

-- #eval IO.println <| Sexp.toString (.app #[.atom (.nat 3),
--   .atom (.str "sdf"), .app #[.atom (.rat 3 10), .atom (.kw "kl"), .atom (.symb "a7&")]])

structure PartialResult where
  -- Lexer state
  lst     : Nat := 0
  -- Partially matched lexicon
  lexpart : String := ""
  -- Parser stack
  pstk    : Array (Array Sexp) := #[]
deriving Inhabited, BEq, Hashable

def PartialResult.toString : PartialResult → String := fun ⟨lst, lexpart, pstk⟩ =>
  s!"PartialResult \{ lst := {lst}, lexpart := {repr lexpart}, pstk := {pstk.toList.map (·.toList)}}"

instance : ToString PartialResult where
  toString := PartialResult.toString

inductive ParseResult where
  -- Sexp: Result
  -- String.pos: The position of the next character
  | complete   : Sexp → String.Pos → ParseResult
  -- Array (Array Sexp): Parser stack
  -- Nat: State of lexer
  -- String.pos: The position of the next character
  | incomplete : PartialResult → String.Pos → ParseResult
  -- Malformed input
  | malformed  : ParseResult
deriving Inhabited, BEq, Hashable

def ParseResult.toString : ParseResult → String
| .complete s p => s!"ParseResult.complete {s} {p}"
| .incomplete pr p => s!"ParseResult.incomplete {pr} {p}"
| .malformed => "ParseResult.malformed"

local instance : Hashable Char := ⟨fun c => hash c.val⟩

/--
  Note: Make sure that the next character of `s` is either `EOF` or white space
  This is because wee rely on the property that:
     For each lexicon `l` with a white space at position `p`, the
     part of `l` before `p` will always be identified as `incomplete`
     by `ERE.ADFALexEagerL SMTSexp.lexiconADFA`, and never as `done`.
-/
def parseSexp (s : String) (p : String.Pos) (partialResult : PartialResult) : ParseResult := Id.run <| do
  if p == s.endPos then
    return .incomplete partialResult p
  let nextLexicon (p : String.Pos) (lst : Nat) :=
    Regex.ERE.ADFALexEagerL SMTSexp.lexiconADFA ⟨s, p, s.endPos⟩
      {strict := true, initS := lst, prependBeginS := false, appendEndS := false}
  let mut lst := partialResult.lst
  let mut lexpart := partialResult.lexpart
  let mut pstk := partialResult.pstk
  let mut p := p
  let endPos := s.endPos
  while true do
    -- If we're not resuming from an incomplete
    --   match of lexicon, skip white space
    if lexpart == "" then
      -- Skip whitespace characters
      while p != endPos do
        let c := s.get! p
        if SMTSexp.whitespace.contains c then
          p := p + c
        else
          break
    -- This indicates incomplete input
    if p == endPos then
      return .incomplete ⟨0, "", pstk⟩ p
    match nextLexicon p lst with
    | ⟨.complete, matched, _, state⟩ =>
      -- A unique attribute should be returned, according to `SMTSexp.lexiconADFA`
      let [attr] := (SMTSexp.lexiconADFA.getAttrs state).toList
        | return panic! s!"parseSexp :: Unexpected error"
      p := matched.stopPos
      let lexval := LexVal.ofString (lexpart ++ matched.toString) attr
      -- Restore lexer state
      lst := 0; lexpart := ""
      match lexval with
      | .lparen =>
        pstk := pstk.push #[]
      | .rparen =>
        if pstk.size == 0 then
          -- Too many right parentheses
          return .malformed
        else
          let final := pstk.back!
          pstk := pstk.pop
          if pstk.size == 0 then
            return .complete (.app final) p
          else
            pstk := pstk.modify (pstk.size - 1) (fun arr => arr.push (.app final))
      | .comment s => pstk := pstk.modify (pstk.size - 1) (fun arr => arr.push (.atom (.comment s)))
      | l       =>
        -- Ordinary lexicons must be separated by whitespace or parentheses
        match s.get? p with
        | some c =>
          if !SMTSexp.whitespace.contains c ∧ c != ')' ∧ c != '(' then
            return .malformed
        | none => pure ()
        if pstk.size == 0 then
          -- An atom
          return .complete (.atom lexval) p
        pstk := pstk.modify (pstk.size - 1) (fun arr => arr.push (.atom l))
    | ⟨.incomplete, m, _, lst'⟩ => return .incomplete ⟨lst', lexpart ++ m.toString, pstk⟩ m.stopPos
    | ⟨.malformed, _, _, _⟩  => return .malformed
  return panic! s!"parseSexp :: Unexpected error when parsing string {s}"

/-

private def testit (s : String) (p : String.Pos) (print := true) : IO Unit := do
  match parseSexp s p {} with
  | .complete e p => if print then IO.println e; IO.println (Substring.toString ⟨s, p, s.endPos⟩)
  | .malformed .. => IO.println "malformed"
  | .incomplete .. => IO.println "incomplete"

def longSexp : Nat → Sexp
| 0 => .atom (.nat 239429)
| 1 => .atom (.str "Mon_\"day")
| 2 => .atom (.symb "🔑🥭🍊")
| n + 3 => .app #[longSexp n, longSexp (n + 1), longSexp (n + 2)]

#eval toString (longSexp 4)
#eval (toString (longSexp 20)).length
#eval testit (toString (longSexp 20)) ⟨0⟩ (print:=false)
#eval testit "djn (abcde |fg| h (12 3) 0x50 34.4 (0b0 x2_& |🍉| \"dl\"\"\")) Not here" ⟨3⟩
#eval testit "(abcde 0x" ⟨0⟩
#eval IO.println <| Regex.ERE.ADFALexEagerL SMTSexp.lexiconADFA "abc".toSubstring {}

def testResume : IO Unit := do
  let strs := ["(abcde\n", "|ab", "\nu\n", "|", "ua", "ab)"]
  let mut pr : PartialResult := {}
  for s in strs do
    IO.println (repr s)
    match parseSexp s ⟨0⟩ pr with
    | .complete se p' =>
      IO.println (repr (toString se));
      IO.println (repr (Substring.toString ⟨s, ⟨0⟩, p'⟩))
      return
    | .incomplete pr' p =>
      if p != s.endPos then
        IO.println s!"Unexpected 1 {p} {s.endPos}"
        return
      pr := pr';
    | .malformed => IO.println "Error: malformed input"; return
  IO.println "Unexpected 2"

#eval testResume

-/

end Parser.SMTSexp

end Auto
