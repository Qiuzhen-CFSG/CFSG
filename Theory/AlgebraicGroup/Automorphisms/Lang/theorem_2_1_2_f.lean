module

public import Theory.AlgebraicGroup.Automorphisms.Lang.theorem_2_1_2_e

/-!
This module isolates `theorem_2_1_2_f` from `Theory.AlgebraicGroup.Automorphisms.Lang`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.
-/

universe u v

set_option warningAsError false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_2_1_2_f
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K)
    (hσ : IsAlgebraicSteinbergEndomorphism σ)
    (hK : Variety.IsConnected K)
    (hbij : Function.Bijective σ.onPoints) :
    ∀ x : Variety.Point K, ∃ g : Variety.Point K,
      x = g * σ.onPoints g⁻¹ := by
  sorry

/- The source says that every positive power is Steinberg; here this is
expanded using the definition of `IsAlgebraicSteinbergEndomorphism` on the
iterated point map, since no separate power wrapper is part of the source
interface. -/

end Theory.AlgebraicGroup
