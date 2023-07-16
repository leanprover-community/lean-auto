import Lean
import Auto.Parser.LeanLex
open Lean

--〈spec_constant〉 ::= 〈numeral〉 | 〈decimal〉 | 〈hexadecimal〉 | 〈binary〉 | 〈string〉
--〈s_expr 〉 ::= 〈spec_constant〉 | 〈symbol〉 | 〈keyword〉 | ( 〈s_expr〉∗ )

namespace Auto.Lexer

namespace SMTSexp

open Regex

def whitespace : String := (String.mk
  ([9, 10, 13, 32].map Char.ofNat))

def unprintable : String := String.mk
  ((127 :: List.range 32).map Char.ofNat)

def numeral : ERE :=
  .plus #[.ofStr "0", .comp #[.inStr "123456789", .star (.ofCC .digit)]]

def decimal : ERE :=
  .comp #[numeral, .inStr ".", ERE.some (.ofCC .digit)]

def hexadecimal : ERE :=
  .comp #[.ofStr "0x", ERE.some (.ofCC .xdigit)]

def binary : ERE :=
  .comp #[.ofStr "0b", ERE.some (.inStr "01")]

-- Characters not allowed within a pair of double quote
private def stringAux : EREBracket :=
  .minus (.inStr ("\"" ++ unprintable)) (.inStr whitespace)

def string : ERE :=
  .star (.comp #[.inStr "\"", .bracketN (.inStr ("\"" ++ unprintable)), .inStr "\""])

private def ssymbchars : EREBracket :=
  .plus #[.cc .alnum, .inStr "~!@$%^&*_-+=<>.?/"]

private def notqsymbchars : EREBracket :=
  .minus (.inStr ("|\\" ++ unprintable)) (.inStr whitespace)

def simpleSymbol : ERE := .star (.bracket ssymbchars)

def quotedSymbol : ERE := .comp #[.inStr "|", .star (.bracketN notqsymbchars), .inStr "|"]

def symbol : ERE := .plus #[simpleSymbol, quotedSymbol]

def keyword : ERE := .comp #[.inStr ":", simpleSymbol]

#eval string.toADFA

end SMTSexp

end Auto.Lexer