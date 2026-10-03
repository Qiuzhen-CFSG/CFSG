module

public import Theory.Representation.CyclicFiveDeterminantExtension
public import Theory.Representation.CyclicFiveExtensionRigidity
public import Theory.Representation.CyclicFiveExtensionDescent

/-!
# Rational quartic extensions through a cyclic-five action

An invariant rational-valued irreducible quartic representation of a finite
group extends irreducibly to its semidirect product by a cyclic group of order
five, with rational character values and determinant one on the complement.

Construct a determinant-one extension using cyclic extension and a determinant
twist. Its irreducible restriction and normalization determine its character
uniquely. Semilinear conjugation therefore fixes the character, and algebraicity
of finite-group character values gives descent to the rationals.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 4, p. 381.
-/

public section

noncomputable section
namespace Representation

variable {K : Type*} [Group K] [Finite K]

/-- An invariant rational irreducible quartic representation has a rational
irreducible extension with determinant one on the order-five complement. -/
theorem exists_cyclicFive_rational_det_one_extension
    (α : Multiplicative (ZMod 5) →* MulAut K)
    (ρ : Representation ℂ K (Fin 4 → ℂ)) [IsIrreducible ρ]
    (hrat : ∀ s, ∃ q : ℚ, ρ.character s = (q : ℂ))
    (hinv : ∀ t s, ρ.character (α t s) = ρ.character s) :
    ∃ σ : Representation ℂ (K ⋊[α] Multiplicative (ZMod 5)) (Fin 4 → ℂ),
      IsIrreducible σ ∧ σ.comp SemidirectProduct.inl = ρ ∧
      (∀ x, ∃ q : ℚ, σ.character x = (q : ℂ)) ∧
      ∀ t, LinearMap.det (σ (SemidirectProduct.inr t)) = 1 := by
  obtain ⟨σ, hirr, hres, hdet⟩ := exists_cyclicFive_det_one_extension α ρ hinv
  let : IsIrreducible (σ.comp SemidirectProduct.inl) := hres.symm ▸ inferInstance
  refine ⟨σ, hirr, hres, ?_, hdet⟩
  apply cyclicFive_character_rational_of_normalized_unique α σ
    (by simpa only [hres] using hrat) hdet
  intro τ hchar hτ
  exact cyclicFive_det_one_extension_character_unique α σ τ hchar hdet hτ

/-- An invariant rational irreducible quartic representation extends rationally
and irreducibly through an action of a cyclic group of order five. -/
theorem exists_cyclicFive_rational_extension
    (α : Multiplicative (ZMod 5) →* MulAut K)
    (ρ : Representation ℂ K (Fin 4 → ℂ)) [IsIrreducible ρ]
    (hrat : ∀ s, ∃ q : ℚ, ρ.character s = (q : ℂ))
    (hinv : ∀ t s, ρ.character (α t s) = ρ.character s) :
    ∃ σ : Representation ℂ (K ⋊[α] Multiplicative (ZMod 5)) (Fin 4 → ℂ),
      IsIrreducible σ ∧ σ.comp SemidirectProduct.inl = ρ ∧
      ∀ x, ∃ q : ℚ, σ.character x = (q : ℂ) := by
  obtain ⟨σ, hirr, hres, hratσ, _⟩ :=
    exists_cyclicFive_rational_det_one_extension α ρ hrat hinv
  exact ⟨σ, hirr, hres, hratσ⟩

end Representation
