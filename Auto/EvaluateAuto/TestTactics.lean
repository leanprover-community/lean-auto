import Lean
import Auto.EvaluateAuto.Result
import Auto.EvaluateAuto.ConstAnalysis
import Auto.EvaluateAuto.EnvAnalysis
import Auto.EvaluateAuto.NameArr
import Auto.EvaluateAuto.CommandAnalysis
open Lean

namespace EvalAuto

section Tactics

  open Elab Tactic

  def useRfl : TacticM Unit := do evalTactic (← `(tactic| intros; rfl))

  def useSimp : TacticM Unit := do evalTactic (← `(tactic| intros; simp))

  def useSimpAll : TacticM Unit := do evalTactic (← `(tactic| intros; simp_all))

  def useSimpAllWithPremises (ci : ConstantInfo) : TacticM Unit := do
    let .some proof := ci.value?
      | throwError "{decl_name%} :: ConstantInfo of {ci.name} has no value"
    let usedThmNames ← (← Expr.getUsedTheorems proof).filterM (fun name =>
      return !(← Name.onlyLogicInType name))
    let usedThmTerms : Array Term := usedThmNames.map (fun name => ⟨mkIdent name⟩)
    evalTactic (← `(tactic| intros; simp_all [$[$usedThmTerms:term],*]))

  private def mkAesopStx (addClauses : Array Syntax) : TSyntax `tactic :=
    let synth : SourceInfo := SourceInfo.synthetic default default false
    TSyntax.mk (
      Syntax.node synth `Aesop.Frontend.Parser.aesopTactic
        #[Syntax.atom synth "aesop", Syntax.node synth `null addClauses]
    )

  /--
    Tactic sequence: `intros; aesop`
    Only guaranteed to work for `aesop @ Lean v4.14.0`
  -/
  def useAesop : TacticM Unit := do
    let aesopStx := mkAesopStx #[]
    let stx ← `(tactic|intros; $aesopStx)
    evalTactic stx

  /--
    Tactic sequence: `intros; aesop (add unsafe premise₁) ⋯ (add unsafe premiseₙ)`
    Only guaranteed to work for `aesop @ Lean v4.14.0`
  -/
  def useAesopWithPremises (ci : ConstantInfo) : TacticM Unit := do
    let .some proof := ci.value?
      | throwError "{decl_name%} :: ConstantInfo of {ci.name} has no value"
    let usedThmNames ← (← Expr.getUsedTheorems proof).filterM (fun name =>
      return !(← Name.onlyLogicInType name))
    let usedThmIdents := usedThmNames.map Lean.mkIdent
    let addClauses := usedThmIdents.map mkAddIdentStx
    let aesopStx := mkAesopStx addClauses
    let stx ← `(tactic|intros; $aesopStx)
    evalTactic stx
  where
    synth : SourceInfo := SourceInfo.synthetic default default false
    mkAddIdentStx (ident : Ident) : Syntax :=
      Syntax.node synth `Aesop.Frontend.Parser.«tactic_clause(Add_)»
        #[Syntax.atom synth "(", Syntax.atom synth "add",
          Syntax.node synth `null
            #[Syntax.node synth `Aesop.Frontend.Parser.rule_expr___
              #[Syntax.node synth `Aesop.Frontend.Parser.feature_
                #[Syntax.node synth `Aesop.Frontend.Parser.phaseUnsafe
                  #[Syntax.atom synth "unsafe"]
                ],
                Syntax.node synth `Aesop.Frontend.Parser.rule_expr_
                  #[Lean.Syntax.node synth `Aesop.Frontend.Parser.featIdent #[ident]]
              ]
            ],
            Syntax.atom synth ")"
        ]

end Tactics

end EvalAuto
