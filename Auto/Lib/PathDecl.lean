import Lean
import Auto.Lib.PathHook
open Lean

namespace Auto

namespace PathDecl

/--
  Return path to the build directory of `lean-auto`
  (presumable `<src-root>/.lake/build`),
  assuming that the built `olean` files are in the `.lake/build/lib`
  folder of the source code folder
-/
def buildDir : CoreM System.FilePath := do
  let mut olean ← Lean.findOLean PathHook.hookName
  let npars := PathHook.hookName.components.length + 2
  for _ in [0:npars] do
    let .some olean' := olean.parent
      | throwError "{decl_name%} :: \"{olean}\" has no parent"
    olean := olean'
  return olean

/--
  Return path to the root of the source code for `lean-auto`,
  assuming that the built `olean` files are in the `.lake/build`
  folder of the source code folder
-/
def root : CoreM System.FilePath := do
  let buildDirVal ← buildDir
  let mut dir := buildDirVal
  for _ in [0:2] do
    let .some dir' := dir.parent
      | throwError "{decl_name%} :: {dir} has no parent"
    dir := dir'
  if buildDirVal.normalize != (dir / ".lake/build").normalize then
    throwError (
      s!"{decl_name%} :: \"{buildDirVal.normalize}\" is not equal to " ++
      s!"\"{dir.normalize}\" / \".lake/build\""
    )
  return dir

end PathDecl

end Auto
