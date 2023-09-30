import Auto.Embedding.LamBase

namespace Auto.Lam2TH0
open Embedding.Lam

-- Identifier mapping
-- Sort : bv n     => s_bv{n}
--        atom n   => s_a{n}
-- Term : bvVal xs => t_bv{0-1 string representation of xs}
--        atom n   => t_a{n}
--        etom n   => t_e{n}

def transLamBaseSort : LamBaseSort → String
| .prop => "$o"
| .int  => "$int"
| .real => "$real"
| .bv n => s!"s_bv{n}"

def transLamSort : LamSort → String
| .atom n => s!"s_a{n}"
| .base b => transLamBaseSort b
| .func s1 s2 => s!"({transLamSort s1} > {transLamSort s2})"

def transCstrReal : CstrReal → String
| .zero => "0.0"
| .one  => "1.0"

def transBitvec (bv : List Bool) : String :=
  String.join (bv.map (fun x => if x then "1" else "0"))

def transLamBaseTerm : LamBaseTerm → Except String String
| .trueE      => .ok s!"$true"
| .falseE     => .ok s!"$false"
| .not        => .ok s!"(~)"
| .and        => .ok s!"(&)"
| .or         => .ok s!"(|)"
| .imp        => .ok s!"(=>)"
| .iff        => .ok s!"(=)" -- Zipperposition seems buggy on (<=>)
| .intVal n   => .ok s!"{n}"
| .realVal cr => .ok s!"{transCstrReal cr}"
| .bvVal v    => .ok s!"t_bv{transBitvec v}"
| .eqI _      => .error "transLamBaseTerm :: eqI should not occur here"
| .forallEI _ => .error "transLamBaseTerm :: forallEI should not occur here"
| .existEI _  => .error "transLamBaseTerm :: existEI should not occur here"
| .eq _       => .ok s!"(=)"
| .forallE _  => .ok s!"!!"
| .existE _   => .ok s!"??"

def transLamTerm (t : LamTerm) (lctx := 0) : Except String String :=
  match t with
  | .atom n      => .ok s!"t_a{n}"
  | .etom n      => .ok s!"t_e{n}"
  | .base b      => transLamBaseTerm b
  | .bvar n      => .ok s!"X{lctx - n}"
  | .lam s t     =>
    match transLamTerm t (lctx + 1) with
    | .ok ts => .ok s!"(^ [X{lctx + 1} : {transLamSort s}] : {ts})"
    | .error e => .error e
  | .app _ t₁ t₂ =>
    match transLamTerm t₁ lctx, transLamTerm t₂ lctx with
    | .ok t₁s, .ok t₂s => .ok s!"({t₁s} @ {t₂s})"
    | .error e, _ => .error e
    | .ok _, .error e => .error e

end Auto.Lam2TH0