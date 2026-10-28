module

public import Theory.Character.ConjClassFunction
public import Theory.Character.CharacterEmbedding
public import Theory.Representation.CoefficientReduction
public import Theory.Representation.ComplementModel
public import Theory.Representation.InjectiveDescent

/-!
# Field models for differences of ordinary characters

An actual complex character which is a difference of two characteristic-zero
field models has a genuine model over the same field. Positivity gives an
injective complex intertwiner, and determinant specialization descends its
existence to the original field. Take an invariant complement there, put it in
finite coordinates, and use compatibility of trace with coefficient extension.

This is the model-construction step in virtual-character descent (Serre,
*Linear Representations of Finite Groups*, Chapter 12).
-/

public section

noncomputable section

namespace Representation

/-- An embedding of field models realizes their character difference over the
same field, without a splitting-field assumption. -/
theorem exists_model_character_sub_of_injective
    {K G : Type*} [Field K] [CharZero K] [Group G] [Finite G]
    (f : K →+* ℂ) {m n : ℕ}
    (ρ : Representation K G (Fin m → K))
    (σ : Representation K G (Fin n → K))
    (i : σ.IntertwiningMap ρ) (hi : Function.Injective i) :
    ∃ k, ∃ τ : Representation K G (Fin k → K),
      characterClassFunction (mapCoefficients f τ) =
        characterClassFunction (mapCoefficients f ρ) -
          characterClassFunction (mapCoefficients f σ) := by
  obtain ⟨k, τ, hτ⟩ := exists_complement_model_of_injective ρ σ i hi
  refine ⟨k, τ, ?_⟩
  funext c
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
  change LinearMap.trace ℂ _ (mapCoefficients f τ g) =
    LinearMap.trace ℂ _ (mapCoefficients f ρ g) -
      LinearMap.trace ℂ _ (mapCoefficients f σ g)
  simp only [mapCoefficients_trace, hτ, map_sub]

/-- An actual complex character represented virtually over a characteristic-zero
field has an actual model over that field. No splitting-field assumption is needed. -/
theorem exists_model_of_isConjCharacter_of_character_sub
    {K G : Type*} [Field K] [CharZero K] [Group G] [Finite G]
    (f : K →+* ℂ) {χ : ConjClassFunction G} (hχ : IsConjCharacter χ)
    {m n : ℕ} (ρ : Representation K G (Fin m → K))
    (σ : Representation K G (Fin n → K))
    (hsub : χ = characterClassFunction (mapCoefficients f ρ) -
      characterClassFunction (mapCoefficients f σ)) :
    ∃ k, ∃ τ : Representation K G (Fin k → K),
      characterClassFunction (mapCoefficients f τ) = χ := by
  have he := exists_injective_intertwiningMap_of_isConjCharacter_sub
    (mapCoefficients f ρ) (mapCoefficients f σ) (hsub ▸ hχ)
  obtain ⟨i, hi⟩ := exists_injective_intertwiner_of_mapCoefficients f σ ρ he
  obtain ⟨k, τ, hτ⟩ := exists_model_character_sub_of_injective f ρ σ i hi
  exact ⟨k, τ, hτ.trans hsub.symm⟩

/-- An irreducible complex character which is a difference of field models
is itself realizable over that field. -/
theorem exists_model_of_isIrreducibleConjCharacter_of_character_sub
    {K G : Type*} [Field K] [CharZero K] [Group G] [Finite G]
    (f : K →+* ℂ) {χ : ConjClassFunction G} (hχ : IsIrreducibleConjCharacter χ)
    {m n : ℕ} (ρ : Representation K G (Fin m → K))
    (σ : Representation K G (Fin n → K))
    (hsub : χ = characterClassFunction (mapCoefficients f ρ) -
      characterClassFunction (mapCoefficients f σ)) :
    ∃ k, ∃ τ : Representation K G (Fin k → K),
      characterClassFunction (mapCoefficients f τ) = χ :=
  exists_model_of_isConjCharacter_of_character_sub f hχ.1 ρ σ hsub

end Representation
