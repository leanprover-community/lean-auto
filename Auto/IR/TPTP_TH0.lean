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
         · transNatConst
         · transIntConst
         · transStringConst
         · transBitVecConst
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

def transBoolConst : BoolConst → String
| .ofProp     => s!"(^ [X : {transLamSort (.base .prop)}] : X)"
| .trueb      => "$true"
| .falseb     => "$false"
| .notb       => "(~)"
| .andb       => "(&)"
| .orb        => "(|)"

def transNatConst : NatConst → String
| .natVal n => s!"t_nat{n}"
| .nadd     => "t_nadd"
| .nsub     => "t_nsub"
| .nmul     => "t_nmul"
| .ndiv     => "t_ndiv"
| .nmod     => "t_nmod"
| .nle      => "t_nle"
| .nlt      => "t_nlt"

def transNatConstSort (nc : NatConst) := transLamSort nc.lamCheck

def transIntConst : IntConst → String
| .intVal n => s!"t_int{n}"
| .iofNat   => "t_iofNat"
| .inegSucc => "t_inegSucc"
| .ineg     => "t_ineg"
| .iabs     => "t_iabs"
| .iadd     => "t_iadd"
| .isub     => "t_isub"
| .imul     => "t_imul"
| .idiv     => "t_idiv"
| .imod     => "t_imod"
| .iediv    => "t_iediv"
| .iemod    => "t_iemod"
| .ile      => "t_ile"
| .ilt      => "t_ilt"

def transIntConstSort (ic : IntConst) := transLamSort ic.lamCheck

def transChar (c : Char) : String :=
  "x" ++ String.mk (Nat.toDigits 16 c.toNat)

def transString (s : String) : String :=
  String.join (s.data.map transChar)

def transStringConst : StringConst → String
| .strVal s  => transString s
| .slength   => "t_slength"
| .sapp      => "t_sapp"
| .sle       => "t_sle"
| .slt       => "t_slt"
| .sprefixof => "t_sprefixof"
| .srepall   => "t_srepall"

def transStringConstSort (sc : StringConst) := transLamSort sc.lamCheck

def transBitVecConst : BitVecConst → String
| .bvVal n i        => s!"t_bvVal_{n}_{i}"
| .bvofNat n        => s!"t_bvofNat_{n}"
| .bvtoNat n        => s!"t_bvtoNat_{n}"
| .bvofInt n        => s!"t_bvofInt_{n}"
| .bvtoInt n        => s!"t_bvtoInt_{n}"
| .bvadd n          => s!"t_bvadd_{n}"
| .bvsub n          => s!"t_bvsub_{n}"
| .bvneg n          => s!"t_bvneg_{n}"
| .bvabs n          => s!"t_bvabs_{n}"
| .bvmul n          => s!"t_bvmul_{n}"
| .bvudiv n         => s!"t_bvudiv_{n}"
| .bvurem n         => s!"t_bvurem_{n}"
| .bvsdiv n         => s!"t_bvsdiv_{n}"
| .bvsrem n         => s!"t_bvsrem_{n}"
| .bvsmod n         => s!"t_bvsmod_{n}"
| .bvult n          => s!"t_bvult_{n}"
| .bvule n          => s!"t_bvule_{n}"
| .bvslt n          => s!"t_bvslt_{n}"
| .bvsle n          => s!"t_bvsle_{n}"
| .bvand n          => s!"t_bvand_{n}"
| .bvor n           => s!"t_bvor_{n}"
| .bvxor n          => s!"t_bvxor_{n}"
| .bvnot n          => s!"t_bvnot_{n}"
| .bvshl n          => s!"t_bvshl_{n}"
| .bvlshr n         => s!"t_bvlshr_{n}"
| .bvashr n         => s!"t_bvashr_{n}"
| .bvrotateLeft w   => s!"t_bvrotateLeft_{w}"
| .bvrotateRight w  => s!"t_bvrotateRight_{w}"
| .bvappend n m     => s!"t_bvappend_{n}_{m}"
| .bvextract n h l  => s!"t_bvextract_{n}_{h}_{l}"
| .bvrepeat w i     => s!"t_bvrepeat_{w}_{i}"
| .bvzeroExtend w v => s!"t_bvzeroExtend_{w}_{v}"
| .bvsignExtend w v => s!"t_bvsignExtend_{w}_{v}"

def transBitVecConstSort (bvc : BitVecConst) := transLamSort bvc.lamCheck

def transLamBaseTerm : LamBaseTerm → Except String String
| .trueE      => .ok s!"$true"
| .falseE     => .ok s!"$false"
| .not        => .ok s!"(~)"
| .and        => .ok s!"(&)"
| .or         => .ok s!"(|)"
| .imp        => .ok s!"(=>)"
| .iff        => .ok s!"(=)" -- Zipperposition seems buggy on (<=>)
| .bcst bc    => .ok (transBoolConst bc)
| .ncst nc    => .ok (transNatConst nc)
| .icst ic    => .ok (transIntConst ic)
| .scst sc    => .ok (transStringConst sc)
| .bvcst bvc  => .ok (transBitVecConst bvc)
| .eqI _      => .error "transLamBaseTerm :: eqI should not occur here"
| .forallEI _ => .error "transLamBaseTerm :: forallEI should not occur here"
| .existEI _  => .error "transLamBaseTerm :: existEI should not occur here"
| .iteI _     => .error "transLamBaseTerm :: iteI should not occur here"
| .eq _       => .ok s!"(=)"
| .forallE s  =>
  if s == .base .empty then
    .ok s!"(^ [EPF : {transLamSort (.func s (.base .prop))}] : $true)"
  else
    .ok s!"!!"
| .existE s   =>
  if s == .base .empty then
    .ok s!"(^ [EPF : {transLamSort (.func s (.base .prop))}] : $false)"
  else
    .ok s!"??"
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