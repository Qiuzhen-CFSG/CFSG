module

public import Theory.AlgebraicGroup.Automorphisms.Classification.theorem_1_15_6

/-!
This module isolates `theorem_1_15_7` from `Theory.AlgebraicGroup.Automorphisms.Classification`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.
-/

set_option warningAsError false

universe u v w

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_1_15_7
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    (classification : RootClassification) (φ : ℤ → Aut K) (ψ : Aut K)
    (hK : IsSimpleAlgebraicGroup K)
    (hCanonical : IsCanonicalSteinbergData D C classification φ ψ) :
    (∃ A : Subgroup (Aut K), (A : Set (Aut K)) = AutOneSet K ∧
      ∀ σ, σ ∈ A → ∀ a, a ∈ AutZero K → σ * a * σ⁻¹ ∈ AutZero K) ∧
    AutOneSet K = setMul (AutZero K : Set (Aut K))
      (S D classification φ ψ) ∧
    (∃ s : Aut K, S D classification φ ψ = (Subgroup.zpowers s : Set (Aut K)) ∧
      (Subgroup.zpowers s : Set (Aut K)).Infinite ∧ IsInfiniteOrderAut s) ∧
    (AutZero K : Set (Aut K)) ∩ S D classification φ ψ = {1} ∧
    SteinbergAutomorphismSet K = setMul (AutZero K : Set (Aut K))
      (SPos D classification φ ψ) ∧
    (∃ f : Aut K, Phi φ = (Subgroup.zpowers f : Set (Aut K)) ∧
      (Phi φ).Infinite) ∧
    (¬ IsExceptionalSteinbergType classification (ringChar k) →
      S D classification φ ψ = Phi φ) ∧
    (IsExceptionalSteinbergType classification (ringChar k) →
      ∃ s : Aut K, S D classification φ ψ = (Subgroup.zpowers s : Set (Aut K)) ∧
        Phi φ = evenPowers s) ∧
    AutOneSet K = setMul (Inn K)
      (setMul (Phi φ) (Gamma D C classification ψ)) ∧
    (∀ p ∈ Phi φ, ∀ γ ∈ Gamma D C classification ψ, p * γ = γ * p) ∧
    ((∃ H : Subgroup (Aut K),
      (H : Set (Aut K)) = setMul (Phi φ) (Gamma D C classification ψ)) ∧
      setMul (Phi φ) (Gamma D C classification ψ) ∩ (Inn K : Set (Aut K)) = {1}) := by sorry

end Theory.AlgebraicGroup
