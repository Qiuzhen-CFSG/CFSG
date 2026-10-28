module

public import Theory.SpecificGroups.PSL2.OuterSolvable.OddCoverage.RootGroups
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# The projective upper-root normalizer

Conjugation by an upper-triangular determinant-one matrix scales the upper-root
parameter by the square of its first diagonal entry. Conversely, in odd
characteristic, a lift taking the upper transvection at one into the upper root
group has lower-left entry zero. Quotient equality up to sign proves the
converse: either the lower-right entries cancel directly, or the lower-left
entry equals its negative. Thus the actual projective root normalizer is the
image of the upper-triangular matrices.

These matrix calculations support both normalization and field recovery in the
A₁ automorphism theorem, GLS3 Theorem 2.5.12 and §2.7.
-/

namespace Theory.PSL2.OuterSolvable.OddCoverage
open Matrix
variable {K : Type*} [Field K]

public theorem sl_conj_upper_of_lowerLeft_zero (A : SpecialLinearGroup (Fin 2) K)
    (hc : A.val 1 0 = 0) (t : K) :
    A * slUpper t * A⁻¹ = slUpper (A.val 0 0 ^ 2 * t) := by
  have had : A.val 0 0 * A.val 1 1 = 1 := by
    simpa only [det_fin_two, hc, mul_zero, sub_zero] using A.property
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  change A.val * (slUpper t).val = (slUpper (A.val 0 0 ^ 2 * t)).val * A.val
  rw [slUpper_val, slUpper_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc]
  linear_combination -(A.val 0 0 * t) * had

public theorem conj_upper_of_lowerLeft_zero (A : SpecialLinearGroup (Fin 2) K)
    (hc : A.val 1 0 = 0) (t : K) :
    quotientMap K A * upper t * (quotientMap K A)⁻¹ = upper (A.val 0 0 ^ 2 * t) := by
  simpa only [map_mul, map_inv, upper] using
    congrArg (quotientMap K) (sl_conj_upper_of_lowerLeft_zero A hc t)

public theorem lowerLeft_zero_of_conj_upper (hchar : ringChar K ≠ 2)
    (A : SpecialLinearGroup (Fin 2) K) (s : K)
    (h : quotientMap K A * upper 1 * (quotientMap K A)⁻¹ = upper s) :
    A.val 1 0 = 0 := by
  have he : quotientMap K (A * slUpper 1) = quotientMap K (slUpper s * A) := by
    simpa only [map_mul, upper] using (mul_inv_eq_iff_eq_mul).mp h
  rcases (quotientMap_eq_iff _ _).mp he with hp | hn
  · have he := congrArg Subtype.val hp
    change A.val * (slUpper 1).val = (slUpper s).val * A.val at he
    rw [slUpper_val, slUpper_val] at he
    have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 1) he
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h11
  · have he := congrArg Subtype.val hn
    change A.val * (slUpper 1).val = -((slUpper s).val * A.val) at he
    rw [slUpper_val, slUpper_val] at he
    have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) he
    have hneg : -(A.val 1 0) = A.val 1 0 := by
      simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h10.symm
    exact (Ring.eq_self_iff_eq_zero_of_char_ne_two hchar).mp hneg

public theorem quotient_mem_rootGroup_normalizer_iff (hchar : ringChar K ≠ 2)
    (A : SpecialLinearGroup (Fin 2) K) :
    quotientMap K A ∈ Subgroup.normalizer (rootGroup K : Set (Group K)) ↔ A.val 1 0 = 0 := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  constructor
  · intro hA
    have hm : quotientMap K A * upper 1 * (quotientMap K A)⁻¹ ∈ rootGroup K := by
      rw [← hA]
      exact ⟨upper 1, (mem_rootGroup _).mpr ⟨1, rfl⟩, rfl⟩
    obtain ⟨s, hs⟩ := (mem_rootGroup _).mp hm
    exact lowerLeft_zero_of_conj_upper hchar A s hs.symm
  · intro hc
    have ha : A.val 0 0 ≠ 0 := by
      intro hzero
      have hd := A.property
      simp only [det_fin_two, hzero, hc, zero_mul, mul_zero, sub_zero, zero_ne_one] at hd
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      obtain ⟨t, rfl⟩ := (mem_rootGroup _).mp hy
      change quotientMap K A * upper t * (quotientMap K A)⁻¹ ∈ rootGroup K
      rw [conj_upper_of_lowerLeft_zero A hc]
      exact (mem_rootGroup _).mpr ⟨_, rfl⟩
    · intro x hx
      obtain ⟨t, rfl⟩ := (mem_rootGroup _).mp hx
      refine ⟨upper (t / A.val 0 0 ^ 2), (mem_rootGroup _).mpr ⟨_, rfl⟩, ?_⟩
      change quotientMap K A * upper (t / A.val 0 0 ^ 2) * (quotientMap K A)⁻¹ = upper t
      rw [conj_upper_of_lowerLeft_zero A hc]
      congr 1
      exact mul_div_cancel₀ t (pow_ne_zero 2 ha)

end Theory.PSL2.OuterSolvable.OddCoverage
