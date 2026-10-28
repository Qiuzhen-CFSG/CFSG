module
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing

/-!
# Five-elements cannot be squared by binary matrix conjugation

For a determinant-one matrix A of size two, Cayley--Hamilton and
tr(A²) = tr(A) force tr(A) to be 2 or -1. In the second case A³ = 1;
in the first, (A-1)² = 0 and A⁵ = 1 imply 5(A-1) = 0. Thus an
order-five element cannot be conjugated to its square outside
characteristic five. The conjugation equality itself forces determinant one.

The Cartan application uses this on the faithful primary Frattini plane
in the nilpotent-Fitting row of Aschbacher--Smith A.3.6, pp.43--45,
while analyzing 11.5.6(3), pp.780--781.
-/

public section
namespace Matrix
variable {F : Type*} [Field F]

/-- The two-dimensional trace restriction, without a group model assumption. -/
theorem eq_one_of_pow_five_of_trace_square
    (a : Matrix (Fin 2) (Fin 2) F) (hfive : (5 : F) ≠ 0)
    (h5 : a ^ 5 = 1) (hd : a.det = 1) (ht : (a ^ 2).trace = a.trace) : a = 1 := by
  have hC : a ^ 2 - a.trace • a + a.det • 1 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two, Matrix.det_fin_two]
      <;> ring
  rw [hd, one_smul] at hC
  have he := congrArg Matrix.trace hC
  simp only [trace_add, trace_sub, trace_smul, trace_one, Fintype.card_fin,
    Nat.cast_ofNat, trace_zero, ht] at he
  have hf : (a.trace - 2) * (a.trace + 1) = 0 := by
    linear_combination -he
  rcases mul_eq_zero.mp hf with ht2 | htn
  · have htr : a.trace = 2 := sub_eq_zero.mp ht2
    simp only [htr, two_smul] at hC
    have hC' : a ^ 2 - 2 * a + 1 = 0 := by simpa only [two_mul] using hC
    have hz : (5 : Matrix (Fin 2) (Fin 2) F) * (a - 1) = 0 := by
      calc
        _ = a ^ 5 - 1 - (a ^ 3 + 2 * a ^ 2 + 3 * a + (1 + 1 + 1 + 1)) *
            (a ^ 2 - 2 * a + 1) := by noncomm_ring
        _ = 0 := by rw [h5, hC']; simp
    have hs : (5 : F) • (a - 1) = 0 := by
      simpa only [Algebra.smul_def, map_ofNat] using hz
    exact sub_eq_zero.mp ((smul_eq_zero.mp hs).resolve_left hfive)
  · have htr : a.trace = -1 := eq_neg_of_add_eq_zero_left htn
    simp only [htr, neg_one_smul, sub_neg_eq_add] at hC
    have h3 : a ^ 3 = 1 := sub_eq_zero.mp (calc
      a ^ 3 - 1 = (a - 1) * (a ^ 2 + a + 1) := by noncomm_ring
      _ = 0 := by rw [hC, mul_zero])
    calc
      a = a ^ 5 * a := by rw [h5, one_mul]
      _ = a ^ 6 := (pow_succ a 5).symm
      _ = (a ^ 3) ^ 2 := (pow_mul a 3 2)
      _ = 1 := by rw [h3, one_pow]
end Matrix

namespace Matrix.GeneralLinearGroup
variable {F : Type*} [Field F]

/-- No binary matrix conjugation squares an element of order five in characteristic other than five. -/
theorem not_conjugate_square_of_order_five
    (a b : GL (Fin 2) F) (hfive : (5 : F) ≠ 0) (ho : orderOf a = 5) :
    b * a * b⁻¹ ≠ a ^ 2 := by
  intro hc
  let d := det (n := Fin 2) (R := F)
  have hde : d a = (d a) ^ 2 := by
    have h := congrArg d hc
    simpa only [map_mul, map_inv, map_pow, mul_comm (d b) (d a),
      mul_inv_cancel_right] using h
  have hdu : d a = 1 := by
    have h := congrArg (fun x => (d a)⁻¹ * x) hde
    simpa only [pow_two, inv_mul_cancel, inv_mul_cancel_left] using h.symm
  have hd : (a : Matrix (Fin 2) (Fin 2) F).det = 1 := congrArg Units.val hdu
  have ha5 : a ^ 5 = 1 := by rw [← ho]; exact pow_orderOf_eq_one a
  have h5 : (a : Matrix (Fin 2) (Fin 2) F) ^ 5 = 1 := congrArg Units.val ha5
  have hv : (b : Matrix (Fin 2) (Fin 2) F) * a * (↑b⁻¹ : Matrix (Fin 2) (Fin 2) F) =
      (a : Matrix (Fin 2) (Fin 2) F) ^ 2 := congrArg Units.val hc
  have ht : ((a : Matrix (Fin 2) (Fin 2) F) ^ 2).trace = (a : Matrix (Fin 2) (Fin 2) F).trace := by
    rw [← hv]
    exact Matrix.trace_units_conj b a
  have hva : (a : Matrix (Fin 2) (Fin 2) F) = 1 :=
    Matrix.eq_one_of_pow_five_of_trace_square (F := F)
      (a : Matrix (Fin 2) (Fin 2) F) hfive h5 hd ht
  have ha : a = 1 := Units.ext hva
  rw [ha, orderOf_one] at ho
  exact (by decide : (1 : ℕ) ≠ 5) ho
end Matrix.GeneralLinearGroup
