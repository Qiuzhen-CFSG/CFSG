module

public import Theory.Representation.SL3.BinaryDefiningFactors
public import Mathlib.RepresentationTheory.Invariants

/-!
# The numerical parabolic bound for non-small SL₃ words

A word with two natural/dual factors or an adjoint factor has degree at least
twice `2^(a+b)`, where a and b are its natural/dual and adjoint counts. Thus an
upper bound of `2^(a+b)` on the literal common fixed space implies a half-degree
bound on fixed codimension. The common-fixed-space estimate itself remains an
explicit premise; it is not inferred from dimensions of the individual factors.

Source: the tensor-degree step of Guralnick–Malle, Classification of 2F-modules
II, author manuscript Proposition 4.7, pp.25–26; Aschbacher–Smith K.3.2,
printed pp.454–456.
-/

@[expose] public section
noncomputable section
open Representation Representation.SL3.BinaryDefiningFactors
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Inner.Coarse

private theorem two_mul_two_pow_le_three_pow {a : ℕ} (ha : 2 ≤ a) :
    2 * 2 ^ a ≤ 3 ^ a := by
  induction a, ha using Nat.le_induction with
  | base => norm_num
  | succ a _ ih =>
    rw [pow_succ, pow_succ]
    calc
      2 * (2 ^ a * 2) = (2 * 2 ^ a) * 2 := by ring
      _ ≤ 3 ^ a * 2 := Nat.mul_le_mul_right 2 ih
      _ ≤ 3 ^ a * 3 := Nat.mul_le_mul_left _ (by decide)

private theorem two_mul_two_pow_le_eight_pow {b : ℕ} (hb : 1 ≤ b) :
    2 * 2 ^ b ≤ 8 ^ b := by
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ b _ ih =>
    rw [pow_succ, pow_succ]
    calc
      2 * (2 ^ b * 2) = (2 * 2 ^ b) * 2 := by ring
      _ ≤ 8 ^ b * 2 := Nat.mul_le_mul_right 2 ih
      _ ≤ 8 ^ b * 8 := Nat.mul_le_mul_left _ (by decide)

/-- Once a word has two natural/dual factors or an adjoint factor, twice the
product of the largest factorwise parabolic fixed dimensions is at most its
degree. This numerical assertion does not assert a tensor fixed-space formula. -/
theorem twice_two_pow_count_le_wordDegree (w : List Factor)
    (hlarge : 2 ≤ naturalCount w ∨ 0 < adjointCount w) :
    2 * 2 ^ (naturalCount w + adjointCount w) ≤ wordDegree w := by
  rw [wordDegree_eq]
  by_cases hb : adjointCount w = 0
  · have ha : 2 ≤ naturalCount w := hlarge.resolve_right (by omega)
    simpa only [hb, Nat.add_zero, pow_zero, mul_one] using two_mul_two_pow_le_three_pow ha
  · have h := Nat.mul_le_mul
      (Nat.pow_le_pow_left (by decide : 2 ≤ 3) (naturalCount w))
      (two_mul_two_pow_le_eight_pow (by omega : 1 ≤ adjointCount w))
    simpa only [pow_add, ← mul_assoc, Nat.mul_comm (2 ^ naturalCount w) 2] using h

/-- The explicit common-fixed-space upper bound gives the needed half-degree
estimate on the actual tensor representation, by rank-nullity. -/
theorem half_degree_of_word_fixed_bound {F K : Type*} [Field F] [Field K] [CharP K 2]
    (ι : F →+* K) (w : List Factor) (A : Subgroup SL(3,F))
    (hlarge : 2 ≤ naturalCount w ∨ 0 < adjointCount w)
    (hfixed : Module.finrank K (invariants ((wordRep ι w).comp A.subtype)) ≤
      2 ^ (naturalCount w + adjointCount w)) :
    Module.finrank K (WordSpace K w) ≤ 2 * Module.finrank K
      (WordSpace K w ⧸ invariants ((wordRep ι w).comp A.subtype)) := by
  have hcount := twice_two_pow_count_le_wordDegree w hlarge
  have hdim := (invariants ((wordRep ι w).comp A.subtype)).finrank_quotient_add_finrank
  rw [finrank_wordSpace] at hdim ⊢
  omega

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Inner.Coarse
