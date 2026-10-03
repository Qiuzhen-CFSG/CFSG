module

public import Stellmacher.Recognition.LyonsU3Four.LocalFiveQuarticExtensionValues
public import Stellmacher.Recognition.LyonsU3Four.LocalFiveQuarticOddValues
public import Theory.Representation.CyclicFiveRationalExtension

/-!
# Assembly of normalized local quartic extensions

Every supplied Sylow quartic character has a normalized rational irreducible
extension to the local group. Realize the Sylow character in dimension four;
its rational value table and invariance under the complement give a rational
extension by the cyclic-five extension theorem. The odd-order value theorem
and the central scalar law then complete the required normalization.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 4, p. 381.
-/

public section
namespace Stellmacher.Recognition.LyonsU3Four
noncomputable section

variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}

/-- Package an actual extension representation, deriving its central value law. -/
theorem IsSylowQuarticCharacter.extension_of_representation
    {z : QuarticCentralIndex S} {θ : ConjClassFunction S}
    (hθ : IsSylowQuarticCharacter S z θ) (h : SylowStructure S)
    (α : FiveComplement →* MulAut S)
    (σ : Representation ℂ (LocalFiveGroup S α) (Fin 4 → ℂ))
    (hirr : Representation.IsIrreducible σ)
    (hres : ∀ s : S, σ.character (SemidirectProduct.inl s) = θ (ConjClasses.mk s))
    (hrat : ∀ x, ∃ q : ℚ, σ.character x = q)
    (hodd : ∀ u, Odd (orderOf u) → u ≠ 1 → σ.character u = -1) :
    IsLocalFiveQuarticExtension S α z θ (characterClassFunction σ) where
  irreducible := ⟨⟨4, σ, rfl⟩, (irreducible_iff_character_norm_one σ).mp hirr⟩
  restriction := hres
  rational := hrat
  odd_value := hodd
  central_mul := hθ.extension_central_mul h α σ hres

/-- Every supplied Sylow quartic character admits a normalized rational
irreducible extension to the local group. -/
theorem IsSylowQuarticCharacter.exists_extension
    {z : QuarticCentralIndex S} {θ : ConjClassFunction S}
    (hθ : IsSylowQuarticCharacter S z θ) (h : SylowStructure S)
    (β : MulAut S) (hβ : orderOf β = 15)
    (α : FiveComplement →* MulAut S)
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ)) :
    ∃ φ : ConjClassFunction (LocalFiveGroup S α),
      IsLocalFiveQuarticExtension S α z θ φ := by
  obtain ⟨ρ, hρ, hchar, _⟩ := hθ.exists_representation h
  let : Representation.IsIrreducible ρ := hρ
  have hval (s : S) : ρ.character s = θ (ConjClasses.mk s) := by
    rw [hchar]
    rfl
  have hratρ : ∀ s, ∃ q : ℚ, ρ.character s = q := by
    intro s
    rw [hval]
    exact hθ.rational s
  have hinv : ∀ t s, ρ.character (α t s) = ρ.character s := by
    intro t s
    rw [hval, hval]
    exact hθ.invariant_under_complement h β hβ α hα t s
  obtain ⟨σ, hirr, hres, hrat⟩ :=
    Representation.exists_cyclicFive_rational_extension α ρ hratρ hinv
  have hresθ : ∀ s : S,
      σ.character (SemidirectProduct.inl s) = θ (ConjClasses.mk s) := by
    intro s
    rw [← hval]
    change Representation.character (σ.comp SemidirectProduct.inl) s = ρ.character s
    rw [hres]
  exact ⟨characterClassFunction σ, hθ.extension_of_representation h α σ hirr hresθ hrat
    (hθ.extension_odd_value h β hβ α hα σ hresθ hrat)⟩

end
end Stellmacher.Recognition.LyonsU3Four
