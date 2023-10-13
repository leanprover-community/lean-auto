import Auto.Embedding.LamConv

namespace Auto.Lam2TH0
open Embedding.Lam

-- Identifier mapping
-- Sort : bv n      => s_bv{n}
--        atom n    => s_a{n}
--        int       => s_int
-- Term : bvVal xs  => t_bv{0-1 string representation of xs}
--        atom n    => t_a{n}
--        etom n    => t_e{n}
--        intVal' n => t_int{n}
--        ineg'     => t_ineg
--        iadd'     => t_iadd
--        isub'     => t_isub
--        imul'     => t_imul
--        idiv'     => t_idiv
--        imod'     => t_imod
--        ile'      => t_ile
--        ilt'      => t_ilt
--        ige'      => t_ige
--        igt'      => t_ige

def transLamBaseSort : LamBaseSort → String
| .prop => "$o"
| .bool => "$o"
| .int  => "s_int"
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

def transBoolConst : BoolConst → String
| .trueb      => "$true"
| .falseb     => "$false"
| .notb       => "(~)"
| .andb       => "(&)"
| .orb        => "(|)"

def transIntConst : IntConst → String
| .intVal n => s!"t_int{n}"
| .ineg     => "t_ineg"
| .iadd     => "t_iadd"
| .isub     => "t_isub"
| .imul     => "t_imul"
| .idiv     => "t_idiv"
| .imod     => "t_imod"
| .ile      => "t_ile"
| .ilt      => "t_ilt"
| .ige      => "t_ige"
| .igt      => "t_igt"

def transIntConstSort : IntConst → String
| .intVal _ => transLamSort (.base .int)
| .ineg     => transLamSort (.func (.base .int) (.base .int))
| .iadd     => transLamSort (.func (.base .int) (.func (.base .int) (.base .int)))
| .isub     => transLamSort (.func (.base .int) (.func (.base .int) (.base .int)))
| .imul     => transLamSort (.func (.base .int) (.func (.base .int) (.base .int)))
| .idiv     => transLamSort (.func (.base .int) (.func (.base .int) (.base .int)))
| .imod     => transLamSort (.func (.base .int) (.func (.base .int) (.base .int)))
| .ile      => transLamSort (.func (.base .int) (.func (.base .int) (.base .prop)))
| .ilt      => transLamSort (.func (.base .int) (.func (.base .int) (.base .prop)))
| .ige      => transLamSort (.func (.base .int) (.func (.base .int) (.base .prop)))
| .igt      => transLamSort (.func (.base .int) (.func (.base .int) (.base .prop)))

def transLamBaseTerm : LamBaseTerm → Except String String
| .trueE      => .ok s!"$true"
| .falseE     => .ok s!"$false"
| .not        => .ok s!"(~)"
| .and        => .ok s!"(&)"
| .or         => .ok s!"(|)"
| .imp        => .ok s!"(=>)"
| .iff        => .ok s!"(=)" -- Zipperposition seems buggy on (<=>)
| .bcst bc    => .ok (transBoolConst bc)
| .icst ic    => .ok (transIntConst ic)
| .realVal cr => .ok s!"{transCstrReal cr}"
| .bvVal v    => .ok s!"t_bv{transBitvec v}"
| .eqI _      => .error "transLamBaseTerm :: eqI should not occur here"
| .forallEI _ => .error "transLamBaseTerm :: forallEI should not occur here"
| .existEI _  => .error "transLamBaseTerm :: existEI should not occur here"
| .eq _       => .ok s!"(=)"
| .forallE _  => .ok s!"!!"
| .existE _   => .ok s!"??"

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
      match transLamTerm (expandQuantBody s body) (lctx + 1) with
      | .ok bs => .ok s!"({qs} [X{lctx} : {transLamSort s}] : {bs})"
      | .error e => .error e
    | .error e => .error e

end Auto.Lam2TH0