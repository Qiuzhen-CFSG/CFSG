module

public import Theory.Character.GaloisScalarProduct
public import Theory.Character.ScalarProductMultiplicity

/-!
# Coefficients of anti-real generalized characters

Complex conjugation pairs the irreducible coefficients of an anti-real
generalized character with their negatives. In particular, a real irreducible
cannot occur. The integrality of character multiplicities is essential here.

Source: ordinary character orthogonality and Galois transport; applied in
P. Fong, *Some Sylow subgroups of order 32 and a characterization of U(3,3)*,
J. Algebra 6 (1967), printed p.73.
-/

public section
noncomputable section
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G]

/-- A generalized character has integral irreducible coefficients. -/
theorem IsGeneralizedCharacter.scalarProduct_irreducible_int
    {Θ χ : ClassFunction G} (hΘ : IsGeneralizedCharacter Θ)
    (hχ : IsIrreducibleCharacter χ) :
    ∃ z : ℤ, scalarProduct G Θ χ = (z : ℂ) := by
  have hc : IsCharacter χ := by
    obtain ⟨n, ρ, _, he⟩ := hχ
    exact ⟨n, ρ, he⟩
  obtain ⟨z, hz⟩ := hc.scalarProduct_generalized_int hΘ
  refine ⟨z, ?_⟩
  rw [← scalarProduct_conj χ Θ, hz]
  simp

/-- Conjugate irreducibles occur with opposite coefficients in an anti-real
generalized character. -/
theorem IsGeneralizedCharacter.scalarProduct_conjugate_of_antiReal
    {Θ χ : ClassFunction G} (hΘ : IsGeneralizedCharacter Θ)
    (hanti : ∀ g, star (Θ g) = -Θ g) (hχ : IsIrreducibleCharacter χ) :
    scalarProduct G Θ (fun g => star (χ g)) = -scalarProduct G Θ χ := by
  obtain ⟨z, hz⟩ := hΘ.scalarProduct_irreducible_int hχ
  have ht := hχ.scalarProduct_comp_ringEquiv (starRingAut : ℂ ≃+* ℂ) Θ
  change scalarProduct G (fun g => star (Θ g)) (fun g => star (χ g)) =
    star (scalarProduct G Θ χ) at ht
  rw [hz, star_intCast] at ht
  have hn : scalarProduct G (fun g => star (Θ g)) (fun g => star (χ g)) =
      -scalarProduct G Θ (fun g => star (χ g)) := by
    simp only [scalarProduct, hanti, neg_mul, Finset.sum_neg_distrib, mul_neg]
  rw [hn] at ht
  rw [hz]
  linear_combination -ht

/-- Real irreducibles have zero coefficient in an anti-real generalized
character. This gives disjointness, not merely orthogonality of two packets. -/
theorem IsGeneralizedCharacter.scalarProduct_eq_zero_of_antiReal_of_real
    {Θ χ : ClassFunction G} (hΘ : IsGeneralizedCharacter Θ)
    (hanti : ∀ g, star (Θ g) = -Θ g) (hχ : IsIrreducibleCharacter χ)
    (hreal : ∀ g, star (χ g) = χ g) : scalarProduct G Θ χ = 0 := by
  have ht := hΘ.scalarProduct_conjugate_of_antiReal hanti hχ
  simp only [hreal] at ht
  linear_combination ht / 2
