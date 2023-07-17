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
| .Atom n    => do
  if !(← hIn n) then
    let name ← h2Symb n
    addCommand (.declFun name #[] (.app (.symb "bool") #[]))
  return .qIdApp (QualIdent.ofString (← h2Symb n)) #[]
| .True      => return .qIdApp (QualIdent.ofString "true") #[]
| .False     => return .qIdApp (QualIdent.ofString "false") #[]
| .Not f     => do
  return .qIdApp (QualIdent.ofString "not") #[← PropForm2STerm f]
| .And f1 f2 => do
  return .qIdApp (QualIdent.ofString "and") #[← PropForm2STerm f1, ← PropForm2STerm f2]
| .Or f1 f2  => do
  return .qIdApp (QualIdent.ofString "or") #[← PropForm2STerm f1, ← PropForm2STerm f2]
| .Iff f1 f2  => do
  return .qIdApp (QualIdent.ofString "not")
    #[.qIdApp (QualIdent.ofString "xor") #[← PropForm2STerm f1, ← PropForm2STerm f2]]
| .Eq f1 f2  => do
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