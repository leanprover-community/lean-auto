import Lean
open Lean

namespace Auto

namespace IR.Smt

inductive Ident where
  -- <index>      ::= <numeral> | <symbol>
  -- <identifier> ::= <symbol> | (_ <symbol> <index>+)
  | symb    : String → Ident
  | indexed : String → (String ⊕ Nat) → Ident

instance : ToString Ident where
  toString : Ident →  String
  | .symb s => "|" ++ s ++ "|"
  | .indexed s idx =>
    match idx with
    | .inl idx => s!"(_ {s} {idx})"
    | .inr idx => s!"(_ {s} {idx})"

inductive Sexp where
  | atom : Ident → Sexp
  | app  : Sexp → Array Sexp → Sexp

partial def Sexp.toString : Sexp → String
| .atom i => ToString.toString i
| .app f arr => "(" ++ String.intercalate " " (#[Sexp.toString f] ++ arr.map Sexp.toString).data ++ ")"

instance : ToString Sexp where
  toString := Sexp.toString

inductive Logic where

structure Query where
  lg        : Logic
  sortdecls : Array (String × Sexp)
  sortdefs  : Array (String × Sexp)
  fundecls  : Array (String × Sexp)
  fundefs   : Array (String × Sexp)

end IR.Smt

end Auto