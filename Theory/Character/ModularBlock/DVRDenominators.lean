module
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Uniform denominator absorption in a discrete valuation ring

For a fixed nonzero denominator in a discrete valuation ring, a single
positive exponent works for every nonunit: its power equals the denominator
times another nonunit. This is the uniform nilpotence input used in proving
primitivity of reduced principal-block selectors.

Write the denominator as a unit times a uniformizer to exponent t, and choose
N = t + 1. A nonzero nonunit has positive uniformizer exponent s, so its
Nth power is divisible by the denominator with quotient exponent
s * (t + 1) - t > 0. The quotient is therefore a nonunit. Zero satisfies
the same conclusion directly.

This ports the exact uniform-exponent lemma from
`Submission/ZStar/BlockPrimitivity.lean` at revision `c3503435` of
`public/lean-eval/glauberman_zStar`. Only DVR arithmetic is used, so the
module is independent of character theory and block constructions.
-/

namespace ModularBlock.BlockPrimitivity

/-- A fixed denominator is absorbed by one power, uniformly in all nonunits,
with a nonunit quotient. -/
public theorem exists_uniform_pow_eq_mul_nonunit
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (n : R) (hn : n ≠ 0) :
    ∃ N : ℕ, 0 < N ∧ ∀ a : R, ¬ IsUnit a →
      ∃ q : R, a ^ N = n * q ∧ ¬ IsUnit q := by
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨t, u, hneq⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hn hpi
  let N := t + 1
  refine ⟨N, by simp [N], ?_⟩
  intro a ha
  by_cases ha0 : a = 0
  · refine ⟨0, ?_, not_isUnit_zero⟩
    simp [ha0]
  obtain ⟨s, v, haeq⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hpi
  have hs : 0 < s := by
    by_contra hs0
    have hs0' : s = 0 := Nat.eq_zero_of_not_pos hs0
    apply ha
    rw [haeq, hs0', pow_zero, mul_one]
    exact v.isUnit
  let k := s * N - t
  let w : Rˣ := u⁻¹ * v ^ N
  refine ⟨(w : R) * pi ^ k, ?_, ?_⟩
  · rw [haeq, hneq, mul_pow, ← pow_mul]
    have hle : t ≤ s * N := by
      dsimp only [N]
      nlinarith
    have htk : t + k = s * N := by
      dsimp only [k]
      omega
    have hpipow : pi ^ (s * N) = pi ^ t * pi ^ k := by
      rw [← htk, pow_add]
    rw [hpipow]
    dsimp only [w]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    have hu : (u : R) * (↑(u⁻¹) : R) = 1 := by simp
    calc
      (v : R) ^ N * (pi ^ t * pi ^ k) =
          ((u : R) * (↑(u⁻¹) : R)) *
            ((v : R) ^ N * (pi ^ t * pi ^ k)) := by rw [hu, one_mul]
      _ = ((u : R) * pi ^ t) *
          (((↑(u⁻¹) : R) * (v : R) ^ N) * pi ^ k) := by ring
  · intro hunit
    have hpowunit : IsUnit (pi ^ k) :=
      (IsUnit.mul_iff.mp hunit).2
    have hk0 : k = 0 :=
      (isUnit_pow_iff_of_not_isUnit hpi.not_isUnit).mp hpowunit
    dsimp only [k, N] at hk0
    have hle : t < s * (t + 1) := by
      nlinarith
    omega

end ModularBlock.BlockPrimitivity

