import Lean
import Auto.Translation.ReifTerms
import Auto.IR.SMT
open Lean

-- P2SMT : Propositional Logic to SMT IR

namespace Auto

-- Open `P`   : To avoid name collision, do not open
-- Open `SMT`
open IR.SMT

private def PropForm2STerm : ReifP.PropForm → TransM Nat STerm
| .atom n    => do
  if !(← hIn n) then
    let name ← h2Symb n
    addCommand (.declFun name #[] (.app (.symb "bool") #[]))
  return .qIdApp (QualIdent.ofString (← h2Symb n)) #[]
| .trueE     => return .qIdApp (QualIdent.ofString "true") #[]
| .falseE    => return .qIdApp (QualIdent.ofString "false") #[]
| .not f     => do
  return .qIdApp (QualIdent.ofString "not") #[← PropForm2STerm f]
| .and f1 f2 => do
  return .qIdApp (QualIdent.ofString "and") #[← PropForm2STerm f1, ← PropForm2STerm f2]
| .or f1 f2  => do
  return .qIdApp (QualIdent.ofString "or") #[← PropForm2STerm f1, ← PropForm2STerm f2]
| .iff f1 f2  => do
  return .qIdApp (QualIdent.ofString "not")
    #[.qIdApp (QualIdent.ofString "xor") #[← PropForm2STerm f1, ← PropForm2STerm f2]]
| .eq f1 f2  => do
  return .qIdApp (QualIdent.ofString "not")
    #[.qIdApp (QualIdent.ofString "xor") #[← PropForm2STerm f1, ← PropForm2STerm f2]]

section

  variable {ω : Type} [BEq ω] [Hashable ω]

  def P2SMT (s : ReifP.State ω) : TransM Nat (Array IR.SMT.Command) := do
    let assertions := s.assertions
    for a in assertions do
      let f ← PropForm2STerm a
      addCommand (.assert f)
    getCommands

end

end Auto