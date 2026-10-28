module

public import Theory.AlgebraicGroup.Automorphisms.Graph

universe u

/-!
Closure and identity cores for the graph-automorphism predicate.

The raw `IsDiagramIsometry` interface records the simple-root and pairing
conditions, but does not yet expose preservation of the chosen negation map.
Consequently multiplication is stated with the exact signed-root preservation
needed by the generator formula rather than silently deriving that missing
root-data fact.
-/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k]

/-- The identity graph automorphism is available for every Chevalley datum. -/
public lemma gammaZeroSet_one_mem
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D) :
    (1 : Aut K) ∈ GammaZeroSet D C := by
  exact ⟨1, isGraphAutomorphism_one D C⟩

/-- Graph automorphisms compose when the second diagram isometry preserves
the signed fundamental roots used by the defining generator formula. -/
public lemma isGraphAutomorphism_mul_of_signed_preservation
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    (ρ σ : Equiv.Perm D.Root) (γ δ : Aut K)
    (hγ : IsGraphAutomorphism D C ρ γ)
    (hδ : IsGraphAutomorphism D C σ δ)
    (hsigned : ∀ α, IsSignedFundamentalRoot D α →
      IsSignedFundamentalRoot D (σ α)) :
    IsGraphAutomorphism D C (ρ * σ) (γ * δ) := by
  refine ⟨(AutZero K).mul_mem hγ.1 hδ.1, ?_, ?_⟩
  · constructor
    · intro α
      simp only [Equiv.Perm.mul_apply]
      exact (hδ.2.1.1 α).trans (hγ.2.1.1 (σ α))
    · intro α β
      simp only [Equiv.Perm.mul_apply]
      rw [hγ.2.1.2, hδ.2.1.2]
  · intro α hα t
    change γ (δ (C.x α t)) = C.x ((ρ * σ) α) t
    rw [hδ.2.2 α hα t, hγ.2.2 (σ α) (hsigned α hα) t]
    rfl

/-- The preceding predicate-level composition result induces closure of the
graph set under the same explicit signed-root preservation hypothesis. -/
public lemma gammaZeroSet_mul_mem_of_signed_preservation
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ρ σ : Equiv.Perm D.Root} {γ δ : Aut K}
    (hγ : IsGraphAutomorphism D C ρ γ)
    (hδ : IsGraphAutomorphism D C σ δ)
    (hsigned : ∀ α, IsSignedFundamentalRoot D α →
      IsSignedFundamentalRoot D (σ α)) :
    γ * δ ∈ GammaZeroSet D C := by
  exact ⟨ρ * σ,
    isGraphAutomorphism_mul_of_signed_preservation D C ρ σ γ δ hγ hδ hsigned⟩

/-- Graph automorphisms invert under the corresponding signed-root
preservation hypothesis. -/
public lemma isGraphAutomorphism_inv_of_signed_preservation
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    (ρ : Equiv.Perm D.Root) (γ : Aut K)
    (hγ : IsGraphAutomorphism D C ρ γ)
    (hsigned : ∀ α, IsSignedFundamentalRoot D α →
      IsSignedFundamentalRoot D (ρ⁻¹ α)) :
    IsGraphAutomorphism D C ρ⁻¹ γ.symm := by
  have hρinv : IsDiagramIsometry D ρ⁻¹ := by
    constructor
    · intro α
      simpa using (hγ.2.1.1 (ρ⁻¹ α)).symm
    · intro α β
      simpa using (hγ.2.1.2 (ρ⁻¹ α) (ρ⁻¹ β)).symm
  refine ⟨(AutZero K).inv_mem hγ.1, hρinv, ?_⟩
  intro α hα t
  apply γ.injective
  simp only [MulEquiv.apply_symm_apply]
  rw [hγ.2.2 (ρ⁻¹ α) (hsigned α hα) t]
  simp

end

end Theory.AlgebraicGroup
