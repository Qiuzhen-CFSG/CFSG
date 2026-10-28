module

public import Theory.AlgebraicGroup.Borel.Conjugation.theorem_1_6_3

/-!
This module isolates `theorem_1_6_4` from `Theory.AlgebraicGroup.Borel.Conjugation`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.
-/

universe u

set_option warningAsError false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_1_6_4
    {G : Variety k} [AlgebraicGroup G]
    {B₁ B₂ T₁ T₂ : ClosedSubgroup G}
    (hB₁ : IsBorelSubgroup B₁) (hB₂ : IsBorelSubgroup B₂)
    (hT₁ : IsTorusMaximalIn T₁ B₁) (hT₂ : IsTorusMaximalIn T₂ B₂) :
    IsMaximalTorus T₁ ∧ IsMaximalTorus T₂ ∧
      ∃ g : Variety.Point G, B₂ = B₁.conjugate g ∧ T₂ = T₁.conjugate g := by sorry

end Theory.AlgebraicGroup
