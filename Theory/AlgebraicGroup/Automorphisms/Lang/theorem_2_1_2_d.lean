module

public import Theory.AlgebraicGroup.Automorphisms.Lang.theorem_2_1_1

/-!
This module isolates `theorem_2_1_2_d` from `Theory.AlgebraicGroup.Automorphisms.Lang`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.
-/

universe u v

set_option warningAsError false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_2_1_2_d
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K)
    (hσ : IsAlgebraicSteinbergEndomorphism σ) :
    ∀ (H : ClosedSubgroup K)
      (hInv : ∀ x : Variety.Point H.carrierVariety,
        σ.onPoints (H.inclusion.onPoints x) ∈ H.toSubgroup),
      ((Variety.IsConnected H.carrierVariety ∨
          IsSemisimpleAlgebraicGroup K ∨ Function.Bijective σ.onPoints) →
        letI := H.carrierAlgebraicGroup
        IsAlgebraicSteinbergEndomorphism
          ((σ.comp H.inclusion).codRestrictClosedSubgroup H hInv)) ∧
      (Variety.IsConnected H.carrierVariety →
        ∀ x : Variety.Point K,
          (σ.onPoints ''
              {y : Variety.Point K |
                ∃ h : Variety.Point K, h ∈ H.toSubgroup ∧ y = x * h}) =
            {y : Variety.Point K |
              ∃ h : Variety.Point K, h ∈ H.toSubgroup ∧ y = x * h} →
          ∃ y : Variety.Point K,
            (∃ h : Variety.Point K, h ∈ H.toSubgroup ∧ y = x * h) ∧
              σ.onPoints y = y) ∧
          (Variety.IsConnected H.carrierVariety → H.toSubgroup.Normal →
        ∃ (Q : Variety k) (_ : AlgebraicGroup Q)
          (π : AlgebraicGroup.Morphism K Q)
          (τ : AlgebraicGroup.Morphism Q Q),
          Function.Surjective π.onPoints ∧
            π.kernel = H.toSubgroup ∧
            (∀ {I : Variety k} (_ : AlgebraicGroup I)
              (φ : AlgebraicGroup.Morphism K I), H.toSubgroup ≤ φ.kernel →
              ∃! ψ : AlgebraicGroup.Morphism Q I, ψ.comp π = φ) ∧
            (∀ x, π.onPoints (σ.onPoints x) = τ.onPoints (π.onPoints x)) ∧
            IsAlgebraicSteinbergEndomorphism τ ∧
            ∀ y, τ.onPoints y = y →
              ∃ x, σ.onPoints x = x ∧ π.onPoints x = y) := by
  sorry

end Theory.AlgebraicGroup
