namespace Auto

structure GLift.{u, v} (α : Sort u) : Sort (max u (v + 1)) where
  /-- Lift a value into `PLift α` -/    up ::
  /-- Extract a value from `PLift α` -/ down : α

def EqLift.{u, v} {α : Sort u} (a b : α) : Type v := GLift (a = b)

def Eq.reflLift.{u, v} {α : Sort u} (a : α) : GLift (a = a) :=
  @GLift.up.{0, v} (a = a) (Eq.refl a)

noncomputable section

def NotLift.{u} (p : GLift.{1, u} Prop) :=
  GLift.up (p.down)

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