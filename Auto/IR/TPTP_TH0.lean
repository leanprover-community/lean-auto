import Auto.Embedding.LamConv

namespace Auto.Lam2TH0
open Embedding.Lam

/-
  Identifier mapping
  Sort : bv n      => s_bv{n}
         atom n    => s_a{n}
         nat       => s_nat
         int       => s_int
         string    => s_string
         empty     => s_empty
  Term : atom n    => t_a{n}
         etom n    => t_e{n}
         Refer to
         · transBoolConst
         · transStringConst
         · transLamBaseTerm
-/

def transLamBaseSort : LamBaseSort → String
| .prop    => "$o"
| .bool    => "$o"
| .nat     => "s_nat"
| .int     => "s_int"
| .isto0 p =>
  match p with
  | .xH => "s_string"
  | .xO .xH => "s_empty"
  | _   => "s_empty"
| .bv n    => s!"s_bv{n}"

def transLamSort : LamSort → String
| .atom n => s!"s_a{n}"
| .base b => transLamBaseSort b
| .func s1 s2 => s!"({transLamSort s1} > {transLamSort s2})"

def transPropConst : PropConst → String
| .trueE      => "$true"
| .falseE     => "$false"
| .not        => "(~)"
| .and        => "(&)"
| .or         => "(|)"
| .imp        => "(=>)"
-- Zipperposition seems buggy on (<=>)
-- Note: At least for some problems, (=) seeems to work better than s!"(^ [L : {transLamSort (.base .prop)}, R : {transLamSort (.base .prop)}] : L = R)"
| .iff        => "(=)"

def transBoolConst : BoolConst → String
| .ofProp     => s!"(^ [X : {transLamSort (.base .prop)}] : X)"
| .trueb      => "$true"
| .falseb     => "$false"
| .notb       => "(~)"
| .andb       => "(&)"
| .orb        => "(|)"

def transNatConst (nc : NatConst) : String := "t_" ++ nc.reprAux.replace " " "_"

def transIntConst (ic : IntConst) : String := "t_" ++ ic.reprAux

def transString (s : String) : String :=
  String.join (s.data.map (fun c => s!"d{c.toNat}"))

def transStringConst : StringConst → String
| .strVal s  => "t_strVal_" ++ transString s
| sc         => "t_" ++ sc.reprAux

def transBitVecConst (bvc : BitVecConst) : String := "t_" ++ bvc.reprAux.replace " " "_"

def transNatConstSort (nc : NatConst) := transLamSort nc.lamCheck

def transIntConstSort (ic : IntConst) := transLamSort ic.lamCheck

def transStringConstSort (sc : StringConst) := transLamSort sc.lamCheck

def transBitVecConstSort (bvc : BitVecConst) := transLamSort bvc.lamCheck

def transLamBaseTerm : LamBaseTerm → Except String String
| .pcst pc    => .ok (transPropConst pc)
| .bcst bc    => .ok (transBoolConst bc)
| .ncst nc    => .ok (transNatConst nc)
| .icst ic    => .ok (transIntConst ic)
| .scst sc    => .ok (transStringConst sc)
| .bvcst bvc  => .ok (transBitVecConst bvc)
-- TODO: translate to λx => x?
| .ocst _     => .error "transLamBaseTerm :: attributes not supported in TPTP"
| .eqI _      => .error "transLamBaseTerm :: eqI should not occur here"
| .forallEI _ => .error "transLamBaseTerm :: forallEI should not occur here"
| .existEI _  => .error "transLamBaseTerm :: existEI should not occur here"
| .iteI _     => .error "transLamBaseTerm :: iteI should not occur here"
| .eq s       => .ok s!"(^ [L : {transLamSort s}, R : {transLamSort s}] : L = R)"
| .forallE s  =>
  if s == .base .empty then
    .ok s!"(^ [EPF : {transLamSort (.func s (.base .prop))}] : $true)"
  else
    .ok s!"(^ [EPF : {transLamSort (.func s (.base .prop))}] : ! [EPX : {transLamSort s}] : (EPF @ EPX))"
| .existE s   =>
  if s == .base .empty then
    .ok s!"(^ [EPF : {transLamSort (.func s (.base .prop))}] : $false)"
  else
    .ok s!"(^ [EPF : {transLamSort (.func s (.base .prop))}] : ? [EPX : {transLamSort s}] : (EPF @ EPX))"
| .ite s      => .ok s!"(^ [IB : {transLamSort (.base .prop)}] : ^ [IX : {transLamSort s}] : ^ [IY : {transLamSort s}] : $ite(IB, IX, IY))"

partial def transLamTerm (t : LamTerm) (lctx := 0) : Except String String :=
  match t with
  | .atom n      => .ok s!"t_a{n}"
  | .etom n      => .ok s!"t_e{n}"
  | .base b      => transLamBaseTerm b
  | .bvar n      => .ok s!"X{lctx - n - 1}"
  | .lam s t     =>
    match transLamTerm t (lctx + 1) with
    | .ok ts => .ok s!"(^ [X{lctx} : {transLamSort s}] : {ts})"
    | .error e => .error e
  | .app _ t₁ t₂ =>
    if t₁.isForallE || t₁.isExistE then
      transQuantApp t₁ t₂ lctx
    else
      match transLamTerm t₁ lctx, transLamTerm t₂ lctx with
      | .ok t₁s, .ok t₂s => .ok s!"({t₁s} @ {t₂s})"
      | .error e, _ => .error e
      | .ok _, .error e => .error e
where
  expandQuantBody (s : LamSort) (t : LamTerm) : LamTerm :=
    match t with
    | .lam _ body => body
    | _ => (LamTerm.app s t (.bvar 0)).headBeta
  transQuantApp (quant body : LamTerm) (lctx : Nat) : Except String String :=
    let info : Except String (String × LamSort) :=
      match quant with
      | .base (.forallE s) => .ok ("!", s)
      | .base (.existE s) => .ok ("?", s)
      | _ => .error "transLamTerm :: Unexpected error"
    match info with
    | .ok (qs, s) =>
      if s == .base .empty then
        match quant with
        | .base (.forallE _) => .ok "$true"
        | .base (.existE _) => .ok "$false"
        | _ => .error "transLamTerm :: Unexpected error"
      else
        match transLamTerm (expandQuantBody s body) (lctx + 1) with
        | .ok bs => .ok s!"({qs} [X{lctx} : {transLamSort s}] : {bs})"
        | .error e => .error e
    | .error e => .error e

end Auto.Lam2TH0
