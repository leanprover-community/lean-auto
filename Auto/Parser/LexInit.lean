import Lean
import Auto.Parser.LeanLex
open Lean

namespace Auto.Lexer

-- SMT-LIB2 compilant lexer
--〈spec_constant〉 ::= 〈numeral〉 | 〈decimal〉 | 〈hexadecimal〉 | 〈binary〉 | 〈string〉
--〈s_expr 〉 ::= 〈spec_constant〉 | 〈symbol〉 | 〈keyword〉 | ( 〈s_expr〉∗ )

-- ⟨index⟩ ::= ⟨numeral⟩ | ⟨symbol⟩
-- ⟨identifier⟩ ::= ⟨symbol⟩ | (_ ⟨symbol⟩ ⟨index⟩+)
-- ⟨sort⟩ ::= ⟨identifier⟩ | (⟨identifier⟩ ⟨sort⟩+)
-- ⟨sorted_var⟩ ::= (⟨symbol⟩ ⟨sort⟩)
-- ⟨var_binding⟩ ::= (⟨symbol⟩ ⟨term⟩)
-- ⟨term⟩ ::= ⟨spec_constant⟩ | (forall (⟨sorted_var⟩+) ⟨term⟩) | (exists (⟨sorted_var⟩+) ⟨term⟩) | (let (⟨var_binding⟩+) ⟨term⟩)

/- Ignored for now:
    - Attributes
    - Qual_identifiers
    - Patterns
    - Match_cases
    - Some of the Term forms that require any of the above -/

namespace SMT

open Regex

def whitespace : String := (String.mk
  ([9, 10, 13, 32].map Char.ofNat))

def unprintable : String := String.mk
  ((127 :: List.range 32).map Char.ofNat)

def comment : ERE :=
  .comp #[.ofStr ";", .star (.bracketN (.inStr "\n")), (.ofStr "\n")]

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

def underscore : ERE := .ofStr "_"

def SMTforall : ERE := .ofStr "forall"
def SMTexists : ERE := .ofStr "exists"
def SMTlambda : ERE := .ofStr "lambda" -- This is not part of SMT-lib 2.6 but can be output by cvc5's hints
def SMTlet : ERE := .ofStr "let"

/-- Special constants -/
def specConst : ERE := .plus #[
  .attr numeral "numeral",
  .attr decimal "decimal",
  .attr hexadecimal "hexadecimal",
  .attr binary "binary",
  .attr string "string"
]

def sexpr : ERE := .plus #[
  specConst,
  -- For lexical analysis, do not distinguish between keyword and symbol
  symbol,
  .attr keyword "keyword",
  .attr lparen "(",
  .attr rparen ")",
  .attr comment "comment"
]

-- ⟨index⟩ ::= ⟨numeral⟩ | ⟨symbol⟩
def index : ERE := .plus #[
  .attr numeral "numeral",
  symbol
]

-- ⟨identifier⟩ ::= ⟨symbol⟩ | (_ ⟨symbol⟩ ⟨index⟩+)
def identifier : ERE := .plus #[
  symbol,
  .attr lparen "(",
  .attr underscore "_",
  .attr rparen ")",
  index
]

-- ⟨sort⟩ ::= ⟨identifier⟩ | (⟨identifier⟩ ⟨sort⟩+)
def sort : ERE := .plus #[
  identifier,
  .attr lparen "(",
  .attr rparen ")"
]

-- ⟨sorted_var⟩ ::= (⟨symbol⟩ ⟨sort⟩)
def sorted_var : ERE := .plus #[
  symbol,
  .attr lparen "(",
  .attr rparen ")",
  sort
]

-- ⟨term⟩ ::= ⟨spec_constant⟩ | ⟨forall (⟨sorted_var⟩+) ⟨term⟩ | ⟨exists (⟨sorted_var⟩+) ⟨term⟩
def term : ERE := .plus #[
  specConst,
  .attr SMTforall "forall",
  .attr SMTexists "exists",
  .attr SMTlambda "lambda",
  .attr SMTlet "let",
  .attr lparen "(",
  .attr rparen ")",
  sorted_var
]

-- Good property: Each state have at most one attribute!
/-
#eval string.toADFA
#eval specConst.toADFA
#eval sexpr.toADFA
#eval identifier.toADFA -- State 6 has two attributes, not sure if that's a problem
#eval sort.toADFA -- State 6 has two attributes, not sure if that's a problem
#eval sorted_var.toADFA -- State 6 has two attributes, not sure if that's a problem
#eval term.toADFA -- States 9, 36, and 37 have multiple attributes, not sure if that's a problem
-/

local instance : Hashable Char where
  hash c := hash c.val

initialize lexiconADFA : ADFA Char ← pure term.toADFA

end SMT

end Auto.Lexer
