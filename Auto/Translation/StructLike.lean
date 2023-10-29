import Lean
import Auto.Lib.ExprExtra
open Lean

/-
  An environment extension to add projections
  for non-structure struct-like inductive types
-/

namespace Auto.StructLike

structure StructLikeFieldInfo where
  fieldName  : Name
  projFn     : Name
  deriving Inhabited, Repr

def StructLikeFieldInfo.lt (i₁ i₂ : StructLikeFieldInfo) : Bool :=
  Name.quickLt i₁.fieldName i₂.fieldName

structure StructLikeInfo where
  structName : Name
  fieldNames : Array Name := #[] -- sorted by field position in the structure
  fieldInfo  : Array StructLikeFieldInfo := #[] -- sorted by `fieldName`
  deriving Inhabited

def StructLikeInfo.lt (i₁ i₂ : StructLikeInfo) : Bool :=
  Name.quickLt i₁.structName i₂.structName

def StructLikeInfo.getProjFn? (info : StructLikeInfo) (i : Nat) : Option Name :=
  if h : i < info.fieldNames.size then
    let fieldName := info.fieldNames.get ⟨i, h⟩
    info.fieldInfo.binSearch { fieldName := fieldName, projFn := default } StructLikeFieldInfo.lt |>.map (·.projFn)
  else
    none

private structure StructLikeState where
  map : PersistentHashMap Name StructLikeInfo := {}
  deriving Inhabited

initialize structLikeExt : SimplePersistentEnvExtension StructLikeInfo StructLikeState ← registerSimplePersistentEnvExtension {
  addImportedFn := fun _ => {}
  addEntryFn    := fun s e => { s with map := s.map.insert e.structName e }
  toArrayFn     := fun es => es.toArray.qsort StructLikeInfo.lt
}

structure StructLikeDescr where
  structName : Name
  fields     : Array StructLikeFieldInfo

def registerStructLike (env : Environment) (e : StructLikeDescr) : Environment :=
  structLikeExt.addEntry env {
    structName := e.structName
    fieldNames := e.fields.map fun e => e.fieldName
    fieldInfo  := e.fields.qsort StructLikeFieldInfo.lt
  }

end Auto.StructLike
