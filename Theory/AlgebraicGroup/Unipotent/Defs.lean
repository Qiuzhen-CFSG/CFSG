module

public import Theory.AlgebraicGroup.Jordan.Basic

universe u

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Definition 1.3.1: every rational point is unipotent. -/
@[expose]
public def IsUnipotentAlgebraicGroup (G : Variety k) [AlgebraicGroup G] : Prop :=
  ∀ g : Variety.Point G, IsUnipotentElement G g

end

end Theory.AlgebraicGroup
