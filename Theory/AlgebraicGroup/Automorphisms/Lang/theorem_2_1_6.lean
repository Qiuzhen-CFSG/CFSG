module

public import Theory.AlgebraicGroup.Automorphisms.Lang.theorem_2_1_4

/-!
This module isolates `theorem_2_1_6` from `Theory.AlgebraicGroup.Automorphisms.Lang`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.
-/

universe u v

set_option warningAsError false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_2_1_6
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K)
    (hσ : IsAlgebraicSteinbergEndomorphism σ)
    (hK : Variety.IsConnected K) :
    (∃ (T B : ClosedSubgroup K),
      IsMaximalTorus T ∧ IsBorelSubgroup B ∧ T ≤ B ∧
      σ.onPoints '' (T : Set (Variety.Point K)) = T ∧
      σ.onPoints '' (B : Set (Variety.Point K)) = B) ∧
    ∀ (T₁ B₁ T₂ B₂ : ClosedSubgroup K),
      IsMaximalTorus T₁ → IsBorelSubgroup B₁ → T₁ ≤ B₁ →
      σ.onPoints '' (T₁ : Set (Variety.Point K)) = T₁ →
      σ.onPoints '' (B₁ : Set (Variety.Point K)) = B₁ →
      IsMaximalTorus T₂ → IsBorelSubgroup B₂ → T₂ ≤ B₂ →
      σ.onPoints '' (T₂ : Set (Variety.Point K)) = T₂ →
      σ.onPoints '' (B₂ : Set (Variety.Point K)) = B₂ →
      ∃ c : Variety.Point K, σ.onPoints c = c ∧
        (fun x => c * x * c⁻¹) '' (T₁ : Set (Variety.Point K)) = T₂ ∧
        (fun x => c * x * c⁻¹) '' (B₁ : Set (Variety.Point K)) = B₂ := by
  sorry

end Theory.AlgebraicGroup
