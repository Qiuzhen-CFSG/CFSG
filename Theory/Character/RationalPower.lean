module

public import Theory.Character.FiniteOrderTrace
public import Theory.Character.ClassFunction
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Rational character values on generators of a cyclic subgroup

A finite-order complex operator with rational trace has the same trace at
all powers coprime to its period. Write its eigenvalues as powers of a
primitive root and form their multiplicity polynomial over the rationals.
Subtracting the trace gives a polynomial divisible by the cyclotomic
polynomial, hence vanishing at every primitive root of that order.

This applies to rational character values without assuming that the
representation has a model over the rationals.

Source: the standard cyclotomic proof of rational power invariance; used in
Fong, *Some Sylow subgroups of order 32 and a characterization of U(3,3)*
(1967), p. 73, the restriction congruences.
-/

public section
noncomputable section
open Polynomial
open scoped BigOperators

/-- Rational trace is invariant under powers coprime to a finite period. -/
theorem finite_order_trace_pow_eq_of_rational
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {n k : ℕ} (hn : n ≠ 0) (hf : f ^ n = 1)
    (hk : k.Coprime n) (hrat : ∃ q : ℚ, LinearMap.trace ℂ V f = (q : ℂ)) :
    LinearMap.trace ℂ V (f ^ k) = LinearMap.trace ℂ V f := by
  classical
  let : NeZero n := ⟨hn⟩
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn
  have he (μ : f.Eigenvalues) : ∃ i < n, ζ ^ i = (μ : ℂ) :=
    hζ.eq_pow_of_pow_eq_one
      (Representation.eigenvalue_pow_eq_one_of_pow_eq_one hf μ.property)
  choose e _ heq using he
  let m (μ : f.Eigenvalues) := Module.finrank ℂ (f.eigenspace (μ : ℂ))
  let P : ℚ[X] := ∑ μ : f.Eigenvalues, monomial (e μ) (m μ : ℚ)
  have hP (j : ℕ) : aeval (ζ ^ j) P = LinearMap.trace ℂ V (f ^ j) := by
    simp only [P, map_sum, aeval_monomial]
    rw [Representation.trace_pow_eq_sum_eigenvalues hn hf]
    apply Finset.sum_congr rfl
    intro μ _
    rw [← pow_mul, Nat.mul_comm j (e μ), pow_mul, heq]
    exact mul_comm _ _
  obtain ⟨q, hq⟩ := hrat
  have hzero : aeval ζ (P - C q) = 0 := by
    have h := hP 1
    simp only [pow_one] at h
    rw [map_sub, h, hq]
    simp
  have hd : cyclotomic n ℚ ∣ P - C q := by
    rw [cyclotomic_eq_minpoly_rat hζ (Nat.pos_of_ne_zero hn)]
    exact minpoly.dvd ℚ ζ hzero
  obtain ⟨Q, hQ⟩ := hd
  have hc : aeval (ζ ^ k) (cyclotomic n ℚ) = 0 := by
    simpa only [aeval_def, eval₂_eq_eval_map, map_cyclotomic, ← IsRoot.def] using
      (hζ.pow_of_coprime k hk).isRoot_cyclotomic (Nat.pos_of_ne_zero hn)
  have hz : aeval (ζ ^ k) (P - C q) = 0 := by
    rw [hQ, map_mul, hc, zero_mul]
  rw [map_sub, hP, aeval_C] at hz
  exact (sub_eq_zero.mp hz).trans hq.symm

/-- A rational character value is the same at every coprime power of an element. -/
theorem IsCharacter.pow_eq_of_rational_value
    {G : Type*} [Group G] {χ : ClassFunction G} (hχ : IsCharacter χ)
    (g : G) {n k : ℕ} (hn : n ≠ 0) (hg : g ^ n = 1) (hk : k.Coprime n)
    (hrat : ∃ q : ℚ, χ g = (q : ℂ)) : χ (g ^ k) = χ g := by
  obtain ⟨d, ρ, rfl⟩ := hχ
  have hρ : (ρ g) ^ n = 1 := by rw [← map_pow, hg, map_one]
  simpa only [Representation.character, map_pow] using
    finite_order_trace_pow_eq_of_rational (ρ g) hn hρ hk hrat

/-- Integer character values in particular are invariant under coprime powers. -/
theorem IsCharacter.pow_eq_of_integer_value
    {G : Type*} [Group G] {χ : ClassFunction G} (hχ : IsCharacter χ)
    (g : G) {n k : ℕ} (hn : n ≠ 0) (hg : g ^ n = 1) (hk : k.Coprime n)
    (hint : ∃ z : ℤ, χ g = (z : ℂ)) : χ (g ^ k) = χ g := by
  apply hχ.pow_eq_of_rational_value g hn hg hk
  obtain ⟨z, hz⟩ := hint
  exact ⟨z, by simpa using hz⟩

/-- An integer character value agrees with the value at the inverse element. -/
theorem IsCharacter.inv_eq_of_integer_value
    {G : Type*} [Group G] [Finite G] {χ : ClassFunction G} (hχ : IsCharacter χ)
    (g : G) (hint : ∃ z : ℤ, χ g = (z : ℂ)) : χ g⁻¹ = χ g := by
  obtain ⟨d, ρ, rfl⟩ := hχ
  obtain ⟨z, hz⟩ := hint
  rw [Representation.representation_character_inv_eq_star_character, hz]
  simp
