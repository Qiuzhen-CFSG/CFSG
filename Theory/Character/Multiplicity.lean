module

public import Theory.Character.Orthogonality

/-!
# Natural character multiplicities

The scalar product of two actual complex characters is a natural number,
the dimension of their intertwining space. The principal scalar product is
the character average, so its vanishing is equivalent to a zero character
sum. These statements apply to restrictions as well as irreducible characters.

Source: the standard intertwiner formula, formalized in Mathlib as
`Representation.card_inv_mul_sum_char_mul_char_eq_finrank`.
-/

open scoped BigOperators
noncomputable section

/-- Scalar products of actual characters are nonnegative integers. -/
public theorem IsCharacter.scalarProduct_eq_nat
    {G : Type*} [Group G] [Fintype G] {χ ψ : ClassFunction G}
    (hχ : IsCharacter χ) (hψ : IsCharacter ψ) :
    ∃ n : ℕ, scalarProduct G χ ψ = (n : ℂ) := by
  obtain ⟨n, ρ, rfl⟩ := hχ
  obtain ⟨m, σ, rfl⟩ := hψ
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  refine ⟨Module.finrank ℂ (Representation.IntertwiningMap σ ρ), ?_⟩
  simp only [scalarProduct,
    ← Representation.representation_character_inv_eq_star_character]
  exact Representation.card_inv_mul_sum_char_mul_char_eq_finrank σ ρ

/-- The constant-one function is an actual character. -/
public theorem principal_isCharacter {G : Type*} [Group G] :
    IsCharacter (1 : ClassFunction G) := by
  refine ⟨1, Representation.trivial ℂ G (Fin 1 → ℂ), ?_⟩
  ext g
  simp [Representation.character]

/-- Vanishing of the principal multiplicity is exactly vanishing of the sum. -/
public theorem scalarProduct_principal_eq_zero_iff
    {G : Type*} [Group G] [Fintype G] (χ : ClassFunction G) :
    scalarProduct G χ 1 = 0 ↔ ∑ g : G, χ g = 0 := by
  simp [scalarProduct]

/-- A nonprincipal irreducible character has zero principal multiplicity. -/
public theorem IsIrreducibleCharacter.scalarProduct_principal_eq_zero
    {G : Type*} [Group G] [Fintype G] {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hne : χ ≠ 1) :
    scalarProduct G χ 1 = 0 := by
  have h1 : IsIrreducibleCharacter (1 : ClassFunction G) := by
    obtain ⟨n, ρ, hρ⟩ := principal_isCharacter (G := G)
    refine ⟨n, ρ, (irreducible_iff_character_norm_one ρ).mpr ?_, hρ⟩
    rw [classFunctionInner_characterClassFunction]
    rw [← hρ]
    simp only [Pi.one_apply, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp only [← Nat.card_eq_fintype_card]
    have hc : (Nat.card G : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := G)).ne'
    simpa only [mul_one] using inv_mul_cancel₀ hc
  simpa [scalarProduct, characterProduct] using
    irreducibleCharacters_orthogonal hχ h1 hne

/-- An irreducible character has strictly positive real degree. -/
public theorem IsIrreducibleConjCharacter.degree_re_pos
    {G : Type*} [Group G] [Finite G] {χ : ConjClassFunction G}
    (hχ : IsIrreducibleConjCharacter χ) : 0 < (χ (ConjClasses.mk 1)).re := by
  obtain ⟨n, ρ, hρ⟩ := hχ.1
  let : Representation.IsIrreducible ρ :=
    (irreducible_iff_character_norm_one ρ).mpr (by simpa [hρ] using hχ.2)
  let : Nontrivial (Fin n → ℂ) := Subrepresentation.irreducible_module_nontrivial ρ
  have hn := Module.finrank_pos (R := ℂ) (M := Fin n → ℂ)
  rw [hρ]
  change 0 < (ρ.character 1).re
  rw [Representation.char_one]
  exact_mod_cast hn
