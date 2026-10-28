module

public import Theory.Character.SchurDegreeTwelve
public import Theory.Character.SimpleCriteria

/-!
# Schur bounds from rationality on odd-order elements

Restriction to an odd Sylow subgroup makes every character value rational.
The prime-power trace spacing and Blichfeldt argument then give Schur's
factorial bound, without requiring a realization over the rationals.
For simple groups, a nonlinear irreducible character supplies faithfulness.

Source: Schur (1905), pp.77–91; ABG III.8 Lemmas 1–2, pp.114–115.
-/

noncomputable section

/-- A nonlinear irreducible conjugacy-class character of a finite simple
group has a faithful complex realization in its specified degree. -/
public theorem IsIrreducibleConjCharacter.exists_faithful_representation
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {χ : ConjClassFunction G} (hχ : IsIrreducibleConjCharacter χ)
    {d : ℕ} (hd : 1 < d) (hdegree : χ (ConjClasses.mk 1) = (d : ℂ)) :
    ∃ ρ : Representation ℂ G (Fin d → ℂ),
      χ = characterClassFunction ρ ∧ Function.Injective ρ := by
  obtain ⟨n, ρ, hρ⟩ := hχ.1
  have hn : n = d := by
    rw [hρ] at hdegree
    change ρ.character 1 = (d : ℂ) at hdegree
    have heq : (n : ℂ) = (d : ℂ) := by
      simpa using hdegree
    exact_mod_cast heq
  subst n
  let : Representation.IsIrreducible ρ :=
    (irreducible_iff_character_norm_one ρ).mpr (by simpa [hρ] using hχ.2)
  exact ⟨ρ, hρ, ρ.injective_of_isSimpleGroup_of_one_lt_finrank (by simpa using hd)⟩

/-- Rationality only on odd-order elements suffices for the odd Sylow
bounds. The representation is complex throughout. -/
public theorem Representation.sylow_card_dvd_pow_mul_factorial_of_odd_rational_character
    {G : Type*} [Group G] [Finite G] {d p : ℕ} [Fact p.Prime]
    (ρ : Representation ℂ G (Fin d → ℂ)) (hfaithful : Function.Injective ρ)
    (hrat : ∀ g : G, Odd (orderOf g) → ∃ q : ℚ, ρ.character g = (q : ℂ))
    (hp : p ≠ 2) (P : Sylow p G) :
    Nat.card P ∣ p ^ (d / (p - 1)) * (d / (p - 1)).factorial := by
  apply Representation.card_dvd_pow_mul_factorial_of_isPGroup
    Fact.out P.isPGroup' (ρ.comp P.toSubgroup.subtype)
    (hfaithful.comp Subtype.val_injective)
  intro g
  obtain ⟨a, ha⟩ := P.isPGroup'.exists_orderOf_dvd_pow g
  have ho : Odd (orderOf (g : G)) := by
    rw [Subgroup.orderOf_coe]
    exact (show Odd (p ^ a) from (Nat.Prime.odd_of_ne_two Fact.out hp).pow).of_dvd_nat ha
  exact hrat g ho

/-- Nonlinear irreducible characters of simple groups satisfy the odd
Sylow bound as soon as their odd-order values are rational. -/
public theorem IsIrreducibleConjCharacter.sylow_card_dvd_of_odd_rational
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {χ : ConjClassFunction G} (hχ : IsIrreducibleConjCharacter χ)
    {d : ℕ} (hd : 1 < d) (hdegree : χ (ConjClasses.mk 1) = (d : ℂ))
    (hrat : ∀ g : G, Odd (orderOf g) → ∃ q : ℚ, χ (ConjClasses.mk g) = (q : ℂ))
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (P : Sylow p G) :
    Nat.card P ∣ p ^ (d / (p - 1)) * (d / (p - 1)).factorial := by
  obtain ⟨ρ, rfl, hf⟩ := hχ.exists_faithful_representation hd hdegree
  exact ρ.sylow_card_dvd_pow_mul_factorial_of_odd_rational_character hf hrat hp P
