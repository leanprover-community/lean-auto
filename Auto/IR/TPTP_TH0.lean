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

def transLamBaseTerm : LamBaseTerm → String
| .trueE      => s!"$true"
| .falseE     => s!"$false"
| .not        => s!"(~)"
| .and        => s!"(&)"
| .or         => s!"(|)"
| .imp        => s!"(=>)"
| .iff        => s!"(=)" -- Zipperposition seems buggy on (<=>)
| .intVal n   => s!"{n}"
| .realVal cr => s!"{transCstrReal cr}"
| .bvVal v    => s!"t_bv{transBitvec v}" 
| .eqI _      => s!"(=)"
| .forallEI _ => s!"!!"
| .existEI _  => s!"??"
| .eq _       => s!"(=)"
| .forallE _  => s!"!!"
| .existE _   => s!"??"

def transLamTerm (t : LamTerm) (lctx := 0) : String :=
  match t with
  | .atom n      => s!"t_a{n}"
  | .etom n      => s!"t_e{n}"
  | .base b      => transLamBaseTerm b
  | .bvar n      => s!"X{lctx - n}"
  | .lam s t     => s!"(^ [X{lctx + 1} : {transLamSort s}] : {transLamTerm t (lctx + 1)})"
  | .app _ t₁ t₂ => s!"({transLamTerm t₁ lctx} @ {transLamTerm t₂ lctx})"

end Auto.Lam2TH0