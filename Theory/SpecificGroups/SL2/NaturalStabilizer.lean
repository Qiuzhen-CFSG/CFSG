module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases

/-!
# Nonzero-vector stabilizers in the natural SL₂ module

Over a field of characteristic two, a determinant-one matrix fixing a nonzero
vector has trace zero and square one. Consequently every nonzero-vector
stabilizer in the natural plane is a two-group. No finiteness or splitting
hypothesis is needed.

The coordinate calculation extends the argument in `SL2.CubicFixedVectors`.
It supplies the natural-module centralizer calculation used in
Aschbacher–Smith, combined manuscript (1 March 2004), E.6.23, printed p.254.
-/

public section

open Matrix
open scoped MatrixGroups

namespace Matrix.SL2
variable {F : Type*} [Field F] [CharP F 2]

/-- A determinant-one matrix fixing a nonzero vector in characteristic two has square one. -/
theorem pow_two_eq_one_of_nonzero_fixed (g : SL(2, F))
    (v : Fin 2 → F) (hne : v ≠ 0) (hv : g.val *ᵥ v = v) : g ^ 2 = 1 := by
  have h0 : g.val 0 0 * v 0 + g.val 0 1 * v 1 = v 0 := by
    simpa [mulVec, dotProduct, Fin.sum_univ_two] using congrFun hv 0
  have h1 : g.val 1 0 * v 0 + g.val 1 1 * v 1 = v 1 := by
    simpa [mulVec, dotProduct, Fin.sum_univ_two] using congrFun hv 1
  have hd : g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0 = 1 :=
    (det_fin_two g.val).symm.trans g.property
  have ht0 : (2 - g.val 0 0 - g.val 1 1) * v 0 = 0 := by
    linear_combination (g.val 1 1 - 1) * h0 - g.val 0 1 * h1 - v 0 * hd
  have ht1 : (2 - g.val 0 0 - g.val 1 1) * v 1 = 0 := by
    linear_combination (g.val 0 0 - 1) * h1 - g.val 1 0 * h0 - v 1 * hd
  have ht : 2 - g.val 0 0 - g.val 1 1 = 0 := by
    by_contra hn
    have hv0 := (mul_eq_zero.mp ht0).resolve_left hn
    have hv1 := (mul_eq_zero.mp ht1).resolve_left hn
    exact hne (by ext i; fin_cases i <;> assumption)
  have h2 : (2 : F) = 0 := by simpa using (CharP.cast_eq_zero F 2)
  have hdiag : g.val 1 1 = g.val 0 0 := by
    rw [h2, zero_sub, CharTwo.neg_eq, sub_eq_zero] at ht
    exact ht.symm
  rw [pow_two]
  apply Subtype.ext
  change g.val * g.val = (1 : Matrix (Fin 2) (Fin 2) F)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  · simpa [hdiag, CharTwo.sub_eq_add] using hd
  · change g.val 0 0 * g.val 0 1 + g.val 0 1 * g.val 1 1 = 0
    rw [hdiag, mul_comm (g.val 0 1) (g.val 0 0), CharTwo.add_self_eq_zero]
  · simp [hdiag, mul_comm, CharTwo.add_self_eq_zero]
  · simpa [hdiag, CharTwo.sub_eq_add, mul_comm, add_comm] using hd

/-- The stabilizer of a nonzero vector in the natural plane is a two-group. -/
theorem stabilizer_nonzero_isPGroup (v : Fin 2 → F) (hv : v ≠ 0) :
    IsPGroup 2 (MulAction.stabilizer SL(2, F) v) := by
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  exact pow_two_eq_one_of_nonzero_fixed g.val v hv g.property
end Matrix.SL2
