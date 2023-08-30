import Lean
open Lean

namespace Auto

def Level.hasCurrentDepthLevelMVar : Level → MetaM Bool
| .zero => pure false
| .succ l => hasCurrentDepthLevelMVar l
| .max l₁ l₂ => or <$> hasCurrentDepthLevelMVar l₁ <*> hasCurrentDepthLevelMVar l₂
| .imax l₁ l₂ => or <$> hasCurrentDepthLevelMVar l₁ <*> hasCurrentDepthLevelMVar l₂
| .param _ => pure false
| .mvar id => not <$> id.isReadOnly

def Level.findParam? (p : Name → Bool) : Level → Option Name
| .zero => .none
| .succ l => findParam? p l
| .max l₁ l₂ => Option.orElse (findParam? p l₁) (fun _ => findParam? p l₂)
| .imax l₁ l₂ => Option.orElse (findParam? p l₁) (fun _ => findParam? p l₂)
| .param name =>
  match p name with
  | true => .some name
  | false => .none
| .mvar _ => .none

end Auto