import Lean
import Auto.Parser.LeanLex
open Lean

namespace Auto.Lexer

-- SMT-LIB2 compilant lexer
--〈spec_constant〉 ::= 〈numeral〉 | 〈decimal〉 | 〈hexadecimal〉 | 〈binary〉 | 〈string〉
--〈s_expr 〉 ::= 〈spec_constant〉 | 〈symbol〉 | 〈keyword〉 | ( 〈s_expr〉∗ )
namespace SMTSexp

open Regex

def whitespace : String := (String.mk
  ([9, 10, 13, 32].map Char.ofNat))

def unprintable : String := String.mk
  ((127 :: List.range 32).map Char.ofNat)

def comment : ERE :=
  .comp #[.ofStr ";", .star $ .bracket (.minus (.cc .all) (.inStr "\n")), (.ofStr "\n")]

def numeral : ERE :=
  .plus #[.ofStr "0", .comp #[.inStr "123456789", .star (.ofCC .digit)]]

def decimal : ERE :=
  .comp #[numeral, .inStr ".", ERE.some (.ofCC .digit)]

def hexadecimal : ERE :=
  .comp #[.ofStr "#x", ERE.some (.ofCC .xdigit)]

def binary : ERE :=
  .comp #[.ofStr "#b", ERE.some (.inStr "01")]

/-- Characters not allowed within a pair of double quote -/
private def stringAux : EREBracket :=
  .minus (.inStr ("\"" ++ unprintable)) (.inStr whitespace)

def string : ERE :=
  .star (.comp #[.inStr "\"", .star (.bracketN (.inStr ("\"" ++ unprintable))), .inStr "\""])

private def ssymbstart : EREBracket :=
  .plus #[.cc .alpha, .inStr "~!@$%^&*_-+=<>.?/"]

private def ssymbchars : EREBracket :=
  .plus #[.cc .alnum, .inStr "~!@$%^&*_-+=<>.?/"]

private def notqsymbchars : EREBracket :=
  .minus (.inStr ("|\\" ++ unprintable)) (.inStr whitespace)

def simpleSymbol : ERE := .comp #[.bracket ssymbstart, .star (.bracket ssymbchars)]

def quotedSymbol : ERE := .comp #[.inStr "|", .star (.bracketN notqsymbchars), .inStr "|"]

def symbol : ERE := .plus #[
  .attr simpleSymbol "simplesymbol",
  .attr quotedSymbol "quotedsymbol"]

def keyword : ERE := .comp #[.inStr ":", simpleSymbol]

def lparen : ERE := .inStr "("

def rparen : ERE := .inStr ")"

/-- Special constants -/
def specConst : ERE := .plus #[
  .attr numeral "numeral",
  .attr decimal "decimal",
  .attr hexadecimal "hexadecimal",
  .attr binary "binary",
  .attr string "string"
]

def lexicons : ERE := .plus #[
  specConst,
  -- For lexical analysis, do not distinguish between keyword and symbol
  symbol,
  .attr keyword "keyword",
  .attr lparen "(",
  .attr rparen ")",
  .attr comment "comment"
]

/-

#eval string.toADFA

#eval specConst.toADFA

-- Good property: Each state have at most one attribute!
#eval lexicons.toADFA

-/

local instance : Hashable Char where
  hash c := hash c.val

initialize lexiconADFA : ADFA Char ← pure lexicons.toADFA

end SMTSexp

end Auto.Lexer
