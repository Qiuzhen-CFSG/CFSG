module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Icosahedral generators over prime fields

For a prime `p > 5` congruent to `±1` modulo five, we construct nontrivial
projective matrices satisfying the `(2,3,5)` relations. This is the matrix
construction underlying Dickson's alternating-five subgroups of `PSL(2,p)`.
The identification with `A₅` requires the independent `(2,3,5)` presentation.

Quadratic reciprocity supplies `t² = t + 1`. Representing `t² - 3` as a sum of
two squares supplies a determinant-one matrix `Y = !![a,b; b-t,1-a]`.
Together with `X = !![0,1; -1,0]`, it satisfies `X² = Y³ = -I` and `(XY)⁵ = I`.
The off-diagonal entry of `X` proves its projective image is nonidentity.

Source: Dickson, *Linear Groups*, the icosahedral subgroup construction;
Thompson's minimal-simple prime-field parameter argument (roadmap M4).
-/

namespace Matrix.SpecialLinearGroup.Icosahedral

open Matrix
open scoped MatrixGroups

private theorem two_ne_zero (p : ℕ) [Fact p.Prime] (hp : 2 < p) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  exact Nat.not_dvd_of_pos_of_lt (by omega : 0 < 2) hp
    ((ZMod.natCast_eq_zero_iff 2 p).mp h)

/-- The golden-ratio equation has a root for the two prime-field residues
that permit icosahedral subgroups. -/
public theorem exists_golden_ratio (p : ℕ) [Fact p.Prime] (hp : 5 < p)
    (hmod : p % 5 = 1 ∨ p % 5 = 4) :
    ∃ t : ZMod p, t ^ 2 = t + 1 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hs : IsSquare (5 : ZMod p) := by
    apply (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p)
      (by norm_num) (by omega)).mp
    have heq : (p : ZMod 5) = ((p % 5 : ℕ) : ZMod 5) := by simp
    rw [heq]
    rcases hmod with h | h
    · rw [h]; exact ⟨1, by norm_num⟩
    · rw [h]; exact ⟨2, by norm_num⟩
  obtain ⟨s, hs⟩ := hs
  have htwo := two_ne_zero p (by omega)
  refine ⟨(1 + s) / 2, ?_⟩
  field_simp
  linear_combination -hs

private theorem exists_coordinates (p : ℕ) [Fact p.Prime] (hp : 2 < p)
    (t : ZMod p) :
    ∃ a b : ZMod p, a * (1 - a) - b * (b - t) = 1 := by
  obtain ⟨u, v, huv⟩ := ZMod.sq_add_sq p (t ^ 2 - 3)
  have htwo := two_ne_zero p hp
  refine ⟨(1 + u) / 2, (t + v) / 2, ?_⟩
  field_simp
  linear_combination -huv

variable {F : Type*} [Field F]

private def x : SL(2,F) := ⟨!![0, 1; -1, 0], by simp⟩

private def y (t a b : F) (h : a * (1 - a) - b * (b - t) = 1) : SL(2,F) :=
  ⟨!![a, b; b - t, 1 - a], by simpa using h⟩

private theorem x_sq : (x : SL(2,F)) ^ 2 = -1 := by
  apply Subtype.ext
  change (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) ^ 2 = -1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

private theorem y_cube (t a b : F) (h : a * (1 - a) - b * (b - t) = 1) :
    (y t a b h) ^ 3 = -1 := by
  apply Subtype.ext
  change (!![a, b; b - t, 1 - a] : Matrix (Fin 2) (Fin 2) F) ^ 3 = -1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;> grind

private theorem xy_fifth (t a b : F) (h : a * (1 - a) - b * (b - t) = 1)
    (ht : t ^ 2 = t + 1) : (x * y t a b h) ^ 5 = 1 := by
  apply Subtype.ext
  change ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) *
    !![a, b; b - t, 1 - a]) ^ 5 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;> grind

private theorem neg_one_mem_center : (-1 : SL(2,F)) ∈ Subgroup.center SL(2,F) := by
  apply SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨-1, by simp, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.coe_neg, Matrix.scalar_apply]

private theorem x_not_mem_center : (x : SL(2,F)) ∉ Subgroup.center SL(2,F) := by
  intro h
  obtain ⟨r, _, hr⟩ := SpecialLinearGroup.mem_center_iff.mp h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hr
  simp [Matrix.scalar_apply, Matrix.diagonal, x] at he

/-- Matrix parameters satisfying the golden-ratio and determinant equations
supply a nontrivial projective representation of the `(2,3,5)` relations. -/
public theorem exists_projective_generators (t a b : F)
    (ht : t ^ 2 = t + 1) (h : a * (1 - a) - b * (b - t) = 1) :
    ∃ X Y : PSL(2,F), X ≠ 1 ∧ X ^ 2 = 1 ∧ Y ^ 3 = 1 ∧ (X * Y) ^ 5 = 1 := by
  let q : SL(2,F) →* PSL(2,F) := QuotientGroup.mk' (Subgroup.center SL(2,F))
  have hneg : q (-1) = 1 := (QuotientGroup.eq_one_iff _).mpr neg_one_mem_center
  refine ⟨q x, q (y t a b h), ?_, ?_, ?_, ?_⟩
  · exact fun hx => x_not_mem_center ((QuotientGroup.eq_one_iff _).mp hx)
  · rw [← map_pow, x_sq, hneg]
  · rw [← map_pow, y_cube, hneg]
  · rw [← map_mul, ← map_pow, xy_fifth t a b h ht, map_one]

/-- Every prime `p > 5` congruent to `±1` modulo five admits nontrivial
projective `(2,3,5)` generators. -/
public theorem exists_projective_generators_prime (p : ℕ) [Fact p.Prime]
    (hp : 5 < p) (hmod : p % 5 = 1 ∨ p % 5 = 4) :
    ∃ X Y : PSL(2,ZMod p), X ≠ 1 ∧ X ^ 2 = 1 ∧ Y ^ 3 = 1 ∧ (X * Y) ^ 5 = 1 := by
  obtain ⟨t, ht⟩ := exists_golden_ratio p hp hmod
  obtain ⟨a, b, hab⟩ := exists_coordinates p (by omega) t
  exact exists_projective_generators t a b ht hab

end Matrix.SpecialLinearGroup.Icosahedral
