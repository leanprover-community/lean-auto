namespace Auto

structure GLift.{u, v} (α : Sort u) : Sort (max u (v + 1)) where
  /-- Lift a value into `GLift α` -/    up ::
  /-- Extract a value from `GLift α` -/ down : α

def EqLift {α : Sort u} (a b : α) : GLift.{1, v} Prop :=
  GLift.up (a = b)

def Eq.reflLift.{u, v} {α : Sort u} (a : GLift.{u, v} α) : GLift (a.down = a.down) :=
  @GLift.up.{0, v} (a.down = a.down) (Eq.refl a.down)

def ForallLift {α : Sort u} (p : α → GLift.{1, v} Prop) : GLift.{1, w} Prop :=
  GLift.up (∀ (x : α), (p x).down)

def ExistsLift {α : Sort u} (p : α → GLift.{1, v} Prop) : GLift.{1, v} Prop :=
  GLift.up (∃ (x : α), (p x).down)

section

def NotLift.{u} (p : GLift.{1, u} Prop) :=
  GLift.up (Not p.down)

def AndLift.{u} (p q : GLift.{1, u} Prop) :=
  GLift.up (And p.down q.down)

def OrLift.{u} (p q : GLift.{1, u} Prop) :=
  GLift.up (Or p.down q.down)

def IffLift.{u} (p q : GLift.{1, u} Prop) :=
  GLift.up (Iff p.down q.down)

def ImpLift.{u} (p q : GLift.{1, u} Prop) :=
  GLift.up (p.down → q.down)

end

end Auto