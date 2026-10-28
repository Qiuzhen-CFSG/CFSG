module

public import Theory.AlgebraicGroup.Borel.Conjugation.theorem_1_6_2_b

/-!
This module isolates `theorem_1_6_3` from `Theory.AlgebraicGroup.Borel.Conjugation`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.
-/

universe u

set_option warningAsError false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_1_6_3
    {G : Variety k} [AlgebraicGroup G] (hG : Variety.IsConnected G)
    (B : ClosedSubgroup G) (hB : IsBorelSubgroup B) :
    ∃ U : ClosedSubgroup G, IsUnipotentRadicalOf B U ∧
      B.normalizer = B ∧
      U.normalizer = B ∧
      ∀ g : Variety.Point G, ∃ x b, b ∈ B.toSubgroup ∧ g = x * b * x⁻¹ := by sorry

end Theory.AlgebraicGroup
