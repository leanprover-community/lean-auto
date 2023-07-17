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
    .str (String.intercalate "" subs)
  | "simplesymbol" => .symb s
  | "quotedsymbol" => .symb ((s.drop 1).take (s.length - 2))
  | "keyword"      => .kw (s.drop 1)
  | _              => panic! s!"LexVal.ofString :: {repr attr} is not a valid attribute"

inductive Sexp where
  | atom : LexVal → Sexp
  | app  : Array Sexp → Sexp
deriving Inhabited, BEq, Hashable

partial def Sexp.toString : Sexp → String
| .atom l => ToString.toString l
| .app ls => "(" ++ String.intercalate " " (ls.map toString).data ++ ")"

instance : ToString Sexp where
  toString e := Sexp.toString e

-- #eval IO.println <| Sexp.toString (.app #[.atom (.nat 3), 
--   .atom (.str "sdf"), .app #[.atom (.rat 3 10), .atom (.kw "kl"), .atom (.symb "a7&")]])

private inductive ParseResult where
  -- Sexp: Result
  -- String.pos: The position of the next character
  | done       : Sexp → String.Pos → ParseResult
  -- Array (Array Sexp): Partial result of parsing
  -- String.pos: The position of the next character
  | incomplete : Array (Array Sexp) → String.Pos → ParseResult
  -- Malformed input
  | malformed  : ParseResult
deriving Inhabited, BEq, Hashable

-- Note: Make sure that the next character of `s` is either `EOF` or line break
-- This is because wee rely on the property that:
--    For each lexicon `l` with a line break at position `p`, the
--    part of `l` before `p` will always be identified as `incomplete`
--    by `ERE.ADFALexEagerL SMTSexp.lexiconADFA`, and never as `done`.
def parseSexp (s : String) (p : String.Pos) (partialResult : Array (Array Sexp)) : ParseResult := Id.run <| do
  let nextLexicon (p : String.Pos) :=
    Regex.ERE.ADFALexEagerL SMTSexp.lexiconADFA ⟨s, p, s.endPos⟩ (strict:=true)
  let mut pr := partialResult
  let mut p := p
  let mut prevp := p
  let endPos := s.endPos
  while true do
    -- Skip whitespace characters
    while p != endPos do
      let c := s.get! p
      if SMTSexp.whitespace.contains c then
        p := p + c
      else
        break
    -- This indicates incomplete input
    if p == endPos then
      return .incomplete pr p
    match nextLexicon p with
    | .done (subs, attrs) =>
      prevp := p
      -- A unique attribute should be returned, according to `SMTSexp.lexiconADFA`
      let [attr] := attrs.toList
        | return panic! "parseSexp :: Unexpected error"
      p := subs.stopPos
      let lexval := LexVal.ofString subs.toString attr
      match lexval with
      | .lparen =>
        pr := pr.push #[]
      | .rparen =>
        if pr.size == 0 then
          -- Too many right parentheses
          return .malformed
        else
          let final := pr.back
          pr := pr.pop
          if pr.size == 0 then
            return .done (.app final) p
          else
            pr := pr.modify (pr.size - 1) (fun arr => arr.push (.app final))
      | l       =>
        -- Ordinary lexicons must be separated by whitespace or parentheses
        match s.get? p with
        | some c =>
          if !SMTSexp.whitespace.contains c ∧ c != ')' ∧ c != '(' then
            return .malformed
        | none => pure ()
        if pr.size == 0 then
          -- An atom
          return .done (.atom lexval) p
        pr := pr.modify (pr.size - 1) (fun arr => arr.push (.atom l))
    | .malformed  => return .malformed
    | .incomplete => return .incomplete pr p
  return panic! "parseSexp :: Unexpected error"

private def testit (s : String) (p : String.Pos) : IO Unit := do
  match parseSexp s p #[] with
  | .done e p => IO.println e; IO.println (Substring.toString ⟨s, p, s.endPos⟩)
  | .malformed .. => IO.println "malformed"
  | .incomplete .. => IO.println "incomplete"

#eval testit "djn (abcde |fg| h (12 3) 0x50 34.4 (0b01 x2_& |🍉|)) Not here" ⟨3⟩
#eval IO.println <| Regex.ERE.ADFALexEagerL SMTSexp.lexiconADFA "abc".toSubstring

end Parser.SMTSexp

end Auto