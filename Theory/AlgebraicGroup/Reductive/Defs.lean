module

public import Theory.AlgebraicGroup.Radical.Defs
public import Theory.AlgebraicGroup.Tori.Basic

universe u

/-! Reductive algebraic groups. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- A reductive algebraic group is connected and has toral radical. -/
@[expose]
public def IsReductiveAlgebraicGroup
    (G : Variety k) [AlgebraicGroup G] : Prop :=
  _root_.IsConnected (Set.univ : Set (Variety.Point G)) ∧
    ∀ R : ClosedSubgroup G, IsRadicalSubgroup R → IsSubtorus R

end Theory.AlgebraicGroup
