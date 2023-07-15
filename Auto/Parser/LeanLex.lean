import Lean
import Auto.Parser.NDFA

-- POSIX ERE internal representation
namespace Auto.Regex

-- Character class
namespace CC

def upper := "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
def lower := "abcdefghijklmnopqrstuvwxyz"
def alpha := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
def digit := "0123456789"
def alnum := alpha ++ digit
def xdigit := "0123456789ABCDEFabcdef"
def punct := ".,!?:…"
def blank := " \t"
def space := " \t\n\r\x0c\x0b"
def cntrl := String.mk ((List.range 32).map Char.ofNat)
def graph := String.mk (((List.range 128).map Char.ofNat).filter (fun x => !" \t\n\r\x0c\x0b".toList.contains x))
def print := String.mk (((List.range 128).map Char.ofNat).filter (fun x => !"\t\n\r\x0c\x0b".toList.contains x))

end CC

section ERE

  variable (σ : Type) [BEq σ] [Hashable σ]

  inductive ERE where
    | any     : ERE
    -- Matches any character contained in the string
    | chars   : σ → ERE
    | startp  : ERE
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
    | comp    : ERE → ERE → ERE
    | add     : ERE → ERE → ERE
  
end ERE

end Auto.Regex