module

public import Theory.Character.Orthogonality

/-!
# Integral character scalar products

The scalar product of two ordinary characters is the dimension of their
intertwiner space. Taking differences gives integer coefficients for generalized
characters. We also record the principal coefficient of a nonprincipal
irreducible minus the principal character.

Source: ordinary character orthogonality; Brauer, *Some applications of the
theory of blocks of characters of finite groups. II* (1964), §V (5.1).
-/

public section
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G]

/-- A scalar product of ordinary characters is a natural multiplicity. -/
theorem IsCharacter.scalarProduct_nat {f g : ClassFunction G}
    (hf : IsCharacter f) (hg : IsCharacter g) : ∃ m : ℕ, scalarProduct G f g = (m : ℂ) := by
  obtain ⟨n, ρ, rfl⟩ := hf
  obtain ⟨m, σ, rfl⟩ := hg
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero
    (by exact_mod_cast (Nat.card_pos (α := G)).ne')
  refine ⟨Module.finrank ℂ (Representation.IntertwiningMap σ ρ), ?_⟩
  simpa only [scalarProduct, ← Representation.representation_character_inv_eq_star_character] using
    Representation.card_inv_mul_sum_char_mul_char_eq_finrank (ρ := σ) (σ := ρ)

/-- Pairing an ordinary character with a generalized character is integral. -/
theorem IsCharacter.scalarProduct_generalized_int {f g : ClassFunction G}
    (hf : IsCharacter f) (hg : IsGeneralizedCharacter g) :
    ∃ z : ℤ, scalarProduct G f g = (z : ℂ) := by
  obtain ⟨g₁, g₂, hg₁, hg₂, rfl⟩ := hg
  obtain ⟨m₁, hm₁⟩ := hf.scalarProduct_nat hg₁
  obtain ⟨m₂, hm₂⟩ := hf.scalarProduct_nat hg₂
  refine ⟨(m₁ : ℤ) - m₂, ?_⟩
  have hsub : scalarProduct G f (g₁ - g₂) = scalarProduct G f g₁ - scalarProduct G f g₂ := by
    simp only [scalarProduct, Pi.sub_apply, star_sub, mul_sub, Finset.sum_sub_distrib]
  rw [hsub, hm₁, hm₂]
  simp

omit [Finite G] in
/-- The constant function one is an irreducible character. -/
theorem isIrreducibleCharacter_one : IsIrreducibleCharacter (1 : ClassFunction G) := by
  refine ⟨1, Representation.trivial ℂ G (Fin 1 → ℂ), ?_, ?_⟩
  · rw [Representation.irreducible_iff_isSimpleModule_asModule, isSimpleModule_iff]
    apply is_simple_module_of_finrank_eq_one (K := ℂ)
    change Module.finrank ℂ (Fin 1 → ℂ) = 1
    simp
  · funext g
    change 1 = LinearMap.trace ℂ (Fin 1 → ℂ) 1
    simp

omit [Finite G] in
/-- The principal character is an ordinary character. -/
theorem isCharacter_one : IsCharacter (1 : ClassFunction G) := by
  obtain ⟨n, ρ, _, hρ⟩ := isIrreducibleCharacter_one (G := G)
  exact ⟨n, ρ, hρ⟩

omit [Finite G] in
/-- Subtracting the principal character gives a generalized character. -/
theorem IsCharacter.sub_one_isGeneralized {ψ : ClassFunction G} (hψ : IsCharacter ψ) :
    IsGeneralizedCharacter (ψ - 1) :=
  ⟨ψ, 1, hψ, isCharacter_one, rfl⟩

/-- The principal coefficient of a nonprincipal irreducible minus one is `-1`. -/
theorem IsIrreducibleCharacter.scalarProduct_one_sub_one {ψ : ClassFunction G}
    (hψ : IsIrreducibleCharacter ψ) (hne : ψ ≠ 1) :
    scalarProduct G 1 (ψ - 1) = -1 := by
  have hzero := irreducibleCharacters_orthogonal isIrreducibleCharacter_one hψ (Ne.symm hne)
  obtain ⟨n, ρ, _, rfl⟩ := hψ
  have hzero' : scalarProduct G 1 ρ.character = 0 := by
    simpa only [scalarProduct, characterProduct,
      Representation.representation_character_inv_eq_star_character] using hzero
  simp only [scalarProduct, Pi.sub_apply, Pi.one_apply, star_sub, star_one, one_mul,
    Finset.sum_sub_distrib, mul_sub] at hzero' ⊢
  rw [hzero']
  simp [← Nat.card_eq_fintype_card,
    (Nat.cast_ne_zero.mpr (Nat.card_pos (α := G)).ne' : (Nat.card G : ℂ) ≠ 0)]
