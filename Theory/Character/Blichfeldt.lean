module

public import Theory.Character.ClassFunction
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Tactic.Ring

/-!
# Character polynomials and Blichfeldt divisibility

The average of an integer polynomial in an ordinary character is an integer:
each power is the character of a tensor power, whose average is the dimension
of its invariant subspace. If the polynomial vanishes on every nonidentity
element, this average is its value at the degree divided by the group order.

This is the character-polynomial argument behind Blichfeldt's divisibility
theorem and the Sylow-group proof of Schur's rational-character order bound
(Schur, *Über eine Klasse von endlichen Gruppen linearen Substitutionen*,
1905, pp. 77–91). No realization over the rationals is required.
-/

open scoped BigOperators
open CategoryTheory.MonoidalCategory

noncomputable section

private theorem exists_fdRep_character_pow
    {G : Type*} [Group G] {χ : ClassFunction G} (hχ : IsCharacter χ) (k : ℕ) :
    ∃ W : FDRep ℂ G, W.character = χ ^ k := by
  obtain ⟨n, ρ, rfl⟩ := hχ
  induction k with
  | zero =>
    refine ⟨FDRep.of (Representation.trivial ℂ G ℂ), ?_⟩
    ext g
    simp [FDRep.character, Representation.trivial]
  | succ k ih =>
    obtain ⟨W, hW⟩ := ih
    refine ⟨W ⊗ FDRep.of ρ, ?_⟩
    rw [FDRep.char_tensor, hW, pow_succ]
    rfl

/-- Averaging an integer polynomial in a character gives an integer. -/
public theorem IsCharacter.integer_average_polynomial
    {G : Type*} [Group G] [Fintype G] {χ : ClassFunction G}
    (hχ : IsCharacter χ) (P : Polynomial ℤ) :
    ∃ a : ℤ, (Nat.card G : ℂ)⁻¹ *
      ∑ g : G, P.eval₂ (Int.castRingHom ℂ) (χ g) = (a : ℂ) := by
  classical
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast (Nat.card_pos (α := G)).ne')
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨a, ha⟩ := hP
    obtain ⟨b, hb⟩ := hQ
    refine ⟨a + b, ?_⟩
    simp only [Polynomial.eval₂_add, Finset.sum_add_distrib, mul_add, ha, hb,
      Int.cast_add]
  | monomial k a =>
    obtain ⟨W, hW⟩ := exists_fdRep_character_pow hχ k
    refine ⟨a * (Module.finrank ℂ (Representation.invariants W.ρ) : ℤ), ?_⟩
    simp only [Polynomial.eval₂_monomial, Int.coe_castRingHom, ← Finset.mul_sum]
    rw [mul_left_comm]
    have havg := W.average_char_eq_finrank_invariants
    rw [hW] at havg
    simpa only [Pi.pow_apply, Int.cast_mul, Int.cast_natCast] using
      congrArg (fun z : ℂ => (a : ℂ) * z) havg

/-- If an integer character polynomial is supported at the identity, its
value at the degree is divisible by the group order. -/
public theorem IsCharacter.card_dvd_polynomial_degree
    {G : Type*} [Group G] [Finite G] {χ : ClassFunction G}
    (hχ : IsCharacter χ) (n : ℕ) (hdegree : χ 1 = (n : ℂ))
    (P : Polynomial ℤ)
    (hvanish : ∀ g : G, g ≠ 1 → P.eval₂ (Int.castRingHom ℂ) (χ g) = 0) :
    (Nat.card G : ℤ) ∣ P.eval (n : ℤ) := by
  classical
  let := Fintype.ofFinite G
  obtain ⟨a, ha⟩ := hχ.integer_average_polynomial P
  have hsum : (∑ g : G, P.eval₂ (Int.castRingHom ℂ) (χ g)) =
      ((P.eval (n : ℤ) : ℤ) : ℂ) := by
    rw [Finset.sum_eq_single 1]
    · rw [hdegree]
      simp
    · intro g _ hg
      exact hvanish g hg
    · simp
  rw [hsum] at ha
  have hc : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  refine ⟨a, ?_⟩
  have heq : ((P.eval (n : ℤ) : ℤ) : ℂ) = (Nat.card G : ℂ) * (a : ℂ) := by
    calc
      _ = (Nat.card G : ℂ) * ((Nat.card G : ℂ)⁻¹ * ((P.eval (n : ℤ) : ℤ) : ℂ)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
      _ = _ := by rw [ha]
  exact_mod_cast heq

/-- Blichfeldt divisibility for a specified finite set of integer character
values away from the identity. -/
public theorem IsCharacter.card_dvd_prod_sub_of_values
    {G : Type*} [Group G] [Finite G] {χ : ClassFunction G}
    (hχ : IsCharacter χ) (n : ℕ) (hdegree : χ 1 = (n : ℂ))
    {ι : Type*} (s : Finset ι) (v : ι → ℤ)
    (hvalues : ∀ g : G, g ≠ 1 → ∃ i ∈ s, χ g = (v i : ℂ)) :
    (Nat.card G : ℤ) ∣ ∏ i ∈ s, ((n : ℤ) - v i) := by
  classical
  let P : Polynomial ℤ := ∏ i ∈ s, (Polynomial.X - Polynomial.C (v i))
  have hvanish : ∀ g : G, g ≠ 1 → P.eval₂ (Int.castRingHom ℂ) (χ g) = 0 := by
    intro g hg
    obtain ⟨i, hi, heq⟩ := hvalues g hg
    simp only [P, Polynomial.eval₂_finsetProd, Polynomial.eval₂_sub,
      Polynomial.eval₂_X, Polynomial.eval₂_C, Int.coe_castRingHom]
    exact Finset.prod_eq_zero hi (by rw [heq, sub_self])
  simpa only [P, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C] using
    hχ.card_dvd_polynomial_degree n hdegree P hvanish

/-- The evenly spaced trace values used in Schur's argument give a factorial
bound on the group order. -/
public theorem IsCharacter.card_dvd_pow_mul_factorial_of_values
    {G : Type*} [Group G] [Finite G] {χ : ClassFunction G}
    (hχ : IsCharacter χ) (n p k : ℕ) (hdegree : χ 1 = (n : ℂ))
    (hvalues : ∀ g : G, g ≠ 1 → ∃ j : ℕ, j < k ∧
      χ g = (n : ℂ) - (p : ℂ) * (j + 1)) :
    Nat.card G ∣ p ^ k * k.factorial := by
  have hd := hχ.card_dvd_prod_sub_of_values n hdegree (Finset.range k)
    (fun j => (n : ℤ) - (p : ℤ) * (j + 1)) (by
      intro g hg
      obtain ⟨j, hj, heq⟩ := hvalues g hg
      exact ⟨j, Finset.mem_range.mpr hj, by simpa using heq⟩)
  have hprod : (∏ j ∈ Finset.range k, ((n : ℤ) - ((n : ℤ) - (p : ℤ) * (j + 1)))) =
      ((p ^ k * k.factorial : ℕ) : ℤ) := by
    simp only [sub_sub_cancel, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range, Nat.cast_mul, Nat.cast_pow]
    congr 1
    exact_mod_cast Finset.prod_range_add_one_eq_factorial k
  rw [hprod] at hd
  exact_mod_cast hd
