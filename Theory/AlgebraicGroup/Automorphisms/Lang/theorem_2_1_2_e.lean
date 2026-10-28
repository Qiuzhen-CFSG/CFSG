module

public import Theory.AlgebraicGroup.Automorphisms.Lang.theorem_2_1_2_d

/-!
This module isolates `theorem_2_1_2_e` from `Theory.AlgebraicGroup.Automorphisms.Lang`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.
-/

universe u v

set_option warningAsError false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_2_1_2_e
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K)
    (hσ : IsAlgebraicSteinbergEndomorphism σ)
    (hK : IsSemisimpleAlgebraicGroup K) :
    ∀ (Ku Ka : Variety k) [AlgebraicGroup Ku] [AlgebraicGroup Ka],
      IsUniversalVersion Ku → IsAdjointVersion Ka →
      ∀ (u : AlgebraicGroup.Morphism Ku K), IsIsogeny u →
      ∀ (a : AlgebraicGroup.Morphism K Ka), IsIsogeny a →
        (∃! σu : AlgebraicGroup.Morphism Ku Ku,
          IsAlgebraicSteinbergEndomorphism σu ∧
            ∀ x, u.onPoints (σu.onPoints x) =
              σ.onPoints (u.onPoints x)) ∧
        (∃! σa : AlgebraicGroup.Morphism Ka Ka,
          IsAlgebraicSteinbergEndomorphism σa ∧
            ∀ x, a.onPoints (σ.onPoints x) =
              σa.onPoints (a.onPoints x)) := by
  sorry

end Theory.AlgebraicGroup
