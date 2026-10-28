module

public import Theory.Character.GaloisConjugation
public import Theory.Character.Integrality
public import Theory.FieldTheory.RationalDescent
public import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Rationality of an irreducible character unique in its degree

Field automorphisms preserve irreducible characters and their degrees, so
uniqueness forces them to fix every value of the given character. Character
values are algebraic integers. Rational descent for algebraic complex numbers
therefore proves that every value is rational, hence an integer.

This is the argument used in Wong (1964), Appendix (b), p. 109, immediately
before equation (14).
-/

public section

/-- A Galois-fixed irreducible character of a finite group is integer-valued. -/
theorem IsIrreducibleCharacter.integer_of_fixed
    {G : Type*} [Group G] [Finite G] {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ)
    (hfixed : ∀ (σ : ℂ ≃+* ℂ) (g : G), σ (χ g) = χ g) :
    ∀ g : G, ∃ a : ℤ, χ g = (a : ℂ) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  intro g
  have hint : IsIntegral ℤ (χ g) := by
    obtain ⟨n, ρ, _, rfl⟩ := hχ
    exact character_value_isIntegral ρ g
  obtain ⟨q, hq⟩ := Complex.exists_ratCast_of_isAlgebraic_of_fixed
    (IsIntegral.tower_top (A := ℚ) hint).isAlgebraic (fun σ => hfixed σ g)
  rw [hq] at hint
  have hqint : IsIntegral ℤ q :=
    (isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective ℚ ℂ)).mp hint
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hqint
  refine ⟨a, ?_⟩
  rw [hq, ← ha]
  simp

/-- An irreducible character unique among irreducible characters of its degree
is rational-valued. -/
theorem IsIrreducibleCharacter.rational_of_unique_degree
    {G : Type*} [Group G] [Finite G] {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ)
    (hunique : ∀ θ : ClassFunction G, IsIrreducibleCharacter θ → θ 1 = χ 1 → θ = χ) :
    ∀ g : G, ∃ q : ℚ, χ g = (q : ℂ) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  intro g
  apply Complex.exists_ratCast_of_isAlgebraic_of_fixed
  · obtain ⟨n, ρ, _, rfl⟩ := hχ
    exact (IsIntegral.tower_top (A := ℚ) (character_value_isIntegral ρ g)).isAlgebraic
  · intro σ
    exact hχ.fixed_of_unique_degree hunique σ g

/-- An irreducible character unique among irreducible characters of its degree
is integer-valued: its rational values are algebraic integers. -/
theorem IsIrreducibleCharacter.integer_of_unique_degree
    {G : Type*} [Group G] [Finite G] {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ)
    (hunique : ∀ θ : ClassFunction G, IsIrreducibleCharacter θ → θ 1 = χ 1 → θ = χ) :
    ∀ g : G, ∃ a : ℤ, χ g = (a : ℂ) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  intro g
  have hint : IsIntegral ℤ (χ g) := by
    obtain ⟨n, ρ, _, rfl⟩ := hχ
    exact character_value_isIntegral ρ g
  obtain ⟨q, hq⟩ := hχ.rational_of_unique_degree hunique g
  rw [hq] at hint
  have hqint : IsIntegral ℤ q :=
    (isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective ℚ ℂ)).mp hint
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hqint
  refine ⟨a, ?_⟩
  rw [hq, ← ha]
  simp
