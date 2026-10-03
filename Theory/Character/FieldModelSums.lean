module

public import Theory.Character.FieldDescent
public import Theory.Representation.CharacterEquivalence

/-!
# Field models for finite integral sums of ordinary characters

An actual complex character expressed as a finite integral combination of
characters of representations over a characteristic-zero field has a model over
that field. The coordinate dimensions of the summands may vary.

Direct products, transferred to finite coordinates, realize sums of characters;
trace transport shows that these sums commute with coefficient extension. Split
each integer coefficient into its positive and negative natural parts, realize
both natural sums, and apply descent for a difference of field models.

This is the integral-sum adapter in virtual-character descent; see Serre,
*Linear Representations of Finite Groups*, Chapter 12.
-/

public section

noncomputable section
open scoped BigOperators
namespace Representation
variable {K G : Type*} [Field K] [Group G]

private theorem model_zero (f : K →+* ℂ) :
    ∃ k, ∃ τ : Representation K G (Fin k → K),
      characterClassFunction (mapCoefficients f τ) = 0 := by
  refine ⟨0, trivial K G (Fin 0 → K), ?_⟩
  funext c
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
  change LinearMap.trace ℂ _ _ = 0
  have h : mapCoefficients f (trivial K G (Fin 0 → K)) g = 0 := Subsingleton.elim _ _
  rw [h, map_zero]

private theorem model_add (f : K →+* ℂ) {m n : ℕ}
    (ρ : Representation K G (Fin m → K))
    (σ : Representation K G (Fin n → K)) :
    ∃ k, ∃ τ : Representation K G (Fin k → K),
      characterClassFunction (mapCoefficients f τ) =
        characterClassFunction (mapCoefficients f ρ) +
        characterClassFunction (mapCoefficients f σ) := by
  let b := Module.finBasis K ((Fin m → K) × (Fin n → K))
  let τ := b.equivFun.conjRingEquiv.toMonoidHom.comp (ρ.prod σ)
  refine ⟨_, τ, ?_⟩
  funext c
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
  change LinearMap.trace ℂ _ (mapCoefficients f τ g) =
    LinearMap.trace ℂ _ (mapCoefficients f ρ g) +
    LinearMap.trace ℂ _ (mapCoefficients f σ g)
  simp only [mapCoefficients_trace]
  change f (LinearMap.trace K _ (b.equivFun.conj (ρ.prod σ g))) = _
  rw [LinearMap.trace_conj']
  have hp := congrFun (character_prod ρ σ) g
  change LinearMap.trace K _ (ρ.prod σ g) =
    LinearMap.trace K _ (ρ g) + LinearMap.trace K _ (σ g) at hp
  rw [hp, map_add]

private theorem model_nsmul (f : K →+* ℂ) {m : ℕ}
    (ρ : Representation K G (Fin m → K)) (a : ℕ) :
    ∃ k, ∃ τ : Representation K G (Fin k → K),
      characterClassFunction (mapCoefficients f τ) =
        a • characterClassFunction (mapCoefficients f ρ) := by
  induction a with
  | zero => simpa using model_zero (G := G) f
  | succ a ih =>
    obtain ⟨k, τ, hτ⟩ := ih
    obtain ⟨l, υ, hυ⟩ := model_add f τ ρ
    exact ⟨l, υ, by rw [hυ, hτ, succ_nsmul]⟩

private theorem model_nat_sum (f : K →+* ℂ) {ι : Type*}
    (s : Finset ι) (m : ι → ℕ)
    (ρ : ∀ j, Representation K G (Fin (m j) → K)) (a : ι → ℕ) :
    ∃ k, ∃ τ : Representation K G (Fin k → K),
      characterClassFunction (mapCoefficients f τ) =
        ∑ j ∈ s, a j • characterClassFunction (mapCoefficients f (ρ j)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using model_zero (G := G) f
  | @insert j s hj ih =>
    obtain ⟨k, τ, hτ⟩ := ih
    obtain ⟨l, υ, hυ⟩ := model_nsmul f (ρ j) (a j)
    obtain ⟨n, σ, hσ⟩ := model_add f υ τ
    exact ⟨n, σ, by rw [hσ, hτ, hυ, Finset.sum_insert hj]⟩

/-- An actual character given by a finite integral sum of field models has a field model. -/
theorem exists_model_of_isConjCharacter_of_finset_int_smul
    [CharZero K] [Finite G] (f : K →+* ℂ)
    {χ : ConjClassFunction G} (hχ : IsConjCharacter χ)
    {ι : Type*} (s : Finset ι) (m : ι → ℕ)
    (ρ : ∀ j, Representation K G (Fin (m j) → K)) (a : ι → ℤ)
    (hsum : χ = ∑ j ∈ s, (a j : ℂ) • characterClassFunction (mapCoefficients f (ρ j))) :
    ∃ k, ∃ τ : Representation K G (Fin k → K),
      characterClassFunction (mapCoefficients f τ) = χ := by
  obtain ⟨p, ρp, hp⟩ := model_nat_sum f s m ρ (fun j => (a j).toNat)
  obtain ⟨n, ρn, hn⟩ := model_nat_sum f s m ρ (fun j => (-a j).toNat)
  apply exists_model_of_isConjCharacter_of_character_sub f hχ ρp ρn
  rw [hp, hn, ← Finset.sum_sub_distrib, hsum]
  apply Finset.sum_congr rfl
  intro j _
  have ha : (a j : ℂ) = ((a j).toNat : ℂ) - ((-a j).toNat : ℂ) := by
    exact_mod_cast (Int.toNat_sub_toNat_neg (a j)).symm
  rw [ha, sub_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

/-- Fintype-indexed version of integral-sum descent for actual characters. -/
theorem exists_model_of_isConjCharacter_of_sum_int_smul
    [CharZero K] [Finite G] (f : K →+* ℂ)
    {χ : ConjClassFunction G} (hχ : IsConjCharacter χ)
    {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (ρ : ∀ j, Representation K G (Fin (m j) → K)) (a : ι → ℤ)
    (hsum : χ = ∑ j, (a j : ℂ) • characterClassFunction (mapCoefficients f (ρ j))) :
    ∃ k, ∃ τ : Representation K G (Fin k → K),
      characterClassFunction (mapCoefficients f τ) = χ :=
  exists_model_of_isConjCharacter_of_finset_int_smul f hχ Finset.univ m ρ a hsum

end Representation
