module

public import Theory.Representation.OrthogonalFourPlusMatrix.Action
public import Theory.Representation.OrthogonalFourPlusMatrix.Comparison.RankOne
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Fixed vectors of determinant point stabilizers

Over a field of characteristic two, the vectors fixed by the stabilizer of a
matrix are perpendicular to that matrix for the polar form of the determinant.
The rank-one orbit reduces the singular case to `E11`; multiplying on the left
reduces the nonsingular case to `diag(det z, 1)`. One upper unipotent in each
stabilizer forces the required entry or diagonal relation.

This is the intrinsic matrix calculation used for the binary hyperplane
argument of Aschbacher–Smith, 9.2.3, combined manuscript (1 March 2004).
-/

@[expose] public noncomputable section

open Matrix
namespace ClassicalOrthogonal.FourPlusMatrix.HyperplaneFixedAux
variable {K : Type*} [Field K]
abbrev polar : Mat (F := K) →ₗ[K] Mat (F := K) →ₗ[K] K :=
  (determinantForm (F := K)).polarBilin

theorem polar_formula [CharP K 2] (x z : Mat (F := K)) :
    polar x z = x 0 0 * z 1 1 + x 1 1 * z 0 0 +
      x 0 1 * z 1 0 + x 1 0 * z 0 1 := by
  simp only [polar, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    determinantForm_apply, det_fin_two, Matrix.add_apply,
    sub_eq_add_neg, CharTwo.neg_eq]
  ring_nf
  simp only [show (2 : K) = 0 from CharP.cast_eq_zero K 2, mul_zero, zero_add, add_zero]

theorem polar_action (a : PairSL (F := K)) (x z : Mat (F := K)) :
    polar (matrixAction a x) (matrixAction a z) = polar x z := by
  simp only [polar, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    determinantForm_apply, ← map_add, matrixAction_det]

private theorem action_mul (a b : PairSL (F := K)) (x : Mat (F := K)) :
    matrixAction (a * b) x = matrixAction a (matrixAction b x) :=
  LinearEquiv.congr_fun (matrixHom.map_mul a b) x

private theorem action_inv_cancel (a : PairSL (F := K)) (x : Mat (F := K)) :
    matrixAction a⁻¹ (matrixAction a x) = x := by
  rw [← action_mul, inv_mul_cancel]
  exact LinearEquiv.congr_fun matrixHom.map_one x

private theorem action_cancel_inv (a : PairSL (F := K)) (x : Mat (F := K)) :
    matrixAction a (matrixAction a⁻¹ x) = x := by
  rw [← action_mul, mul_inv_cancel]
  exact LinearEquiv.congr_fun matrixHom.map_one x

private def upper (a : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1,a;0,1], by simp [det_fin_two]⟩

private theorem action_eq_iff (a : PairSL (F := K)) (x y : Mat (F := K)) :
    matrixAction a x = y ↔ a.1.val * x = y * a.2.val := by
  change a.1.val * x * a.2⁻¹.val = y ↔ _
  constructor
  · intro h
    have he := congrArg (fun Z : Mat (F := K) => Z * a.2.val) h
    simpa only [mul_assoc, ← SpecialLinearGroup.coe_mul, inv_mul_cancel,
      SpecialLinearGroup.coe_one, mul_one] using he
  · intro h
    rw [h, mul_assoc, ← SpecialLinearGroup.coe_mul, mul_inv_cancel,
      SpecialLinearGroup.coe_one, mul_one]

private theorem fixed_transport (a : PairSL (F := K)) (z x : Mat (F := K))
    (h : ∀ b, matrixAction b z = z → matrixAction b x = x) :
    ∀ b, matrixAction b (matrixAction a⁻¹ z) = matrixAction a⁻¹ z →
      matrixAction b (matrixAction a⁻¹ x) = matrixAction a⁻¹ x := by
  intro b hb
  have hfix : matrixAction (a * b * a⁻¹) z = z := by
    rw [action_mul, action_mul, hb, action_cancel_inv]
  have hx := congrArg (matrixAction a⁻¹) (h _ hfix)
  simpa only [action_mul, action_inv_cancel] using hx

theorem polar_zero_of_fixed [CharP K 2] (z x : Mat (F := K))
    (h : ∀ a, matrixAction a z = z → matrixAction a x = x) : polar z x = 0 := by
  by_cases hz : z = 0
  · simp [hz]
  by_cases hd : z.det = 0
  · obtain ⟨A, B, he⟩ :=
      ComparisonAux.MatrixTwo.singular_nonzero_SL2_orbit z hz hd
    let a : PairSL (F := K) := (A, B)
    have haz : z = matrixAction a ComparisonAux.MatrixTwo.E11 := he
    have hbase : matrixAction a⁻¹ z = ComparisonAux.MatrixTwo.E11 := by
      rw [haz, action_inv_cancel]
    let y := matrixAction a⁻¹ x
    have hy := fixed_transport a z x h (upper 1, 1)
    rw [hbase] at hy
    have hu : matrixAction (upper (1 : K), 1) ComparisonAux.MatrixTwo.E11 =
        ComparisonAux.MatrixTwo.E11 := by
      apply (action_eq_iff _ _ _).mpr
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [upper, ComparisonAux.MatrixTwo.E11, mul_apply, Fin.sum_univ_two]
    have hy' := congrArg (fun M : Mat (F := K) => M 0 1)
      ((action_eq_iff _ _ _).mp (hy hu))
    have h11 : y 1 1 = 0 := by
      simpa [y, upper, mul_apply, Fin.sum_univ_two] using hy'
    have hp := polar_action a⁻¹ z x
    rw [hbase] at hp
    rw [← hp, polar_formula]
    simpa [ComparisonAux.MatrixTwo.E11] using h11
  · let d := z.det
    let D : Mat (F := K) := !![d,0;0,1]
    let C : Mat (F := K) := !![d⁻¹,0;0,1]
    have hd' : d ≠ 0 := hd
    have hCD : C * D = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [D, C, mul_apply, Fin.sum_univ_two, hd']
    let A : SpecialLinearGroup (Fin 2) K := ⟨z * C, by
      rw [det_mul]
      have hC : C.det = d⁻¹ := by simp [C, det_fin_two]
      rw [hC]
      exact mul_inv_cancel₀ hd⟩
    let a : PairSL (F := K) := (A, 1)
    have haz : matrixAction a D = z := by
      change z * C * D * (1 : SpecialLinearGroup (Fin 2) K)⁻¹.val = z
      rw [inv_one, SpecialLinearGroup.coe_one, mul_one, mul_assoc, hCD, mul_one]
    have hbase : matrixAction a⁻¹ z = D := by rw [← haz, action_inv_cancel]
    let y := matrixAction a⁻¹ x
    have hy := fixed_transport a z x h (upper d, upper 1)
    rw [hbase] at hy
    have hu : matrixAction (upper d, upper (1 : K)) D = D := by
      apply (action_eq_iff _ _ _).mpr
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [upper, D, mul_apply, Fin.sum_univ_two]
    have hy' := congrArg (fun M : Mat (F := K) => M 0 1)
      ((action_eq_iff _ _ _).mp (hy hu))
    have hdiag : d * y 1 1 = y 0 0 := by
      have hh : y 0 1 + d * y 1 1 = y 0 0 + y 0 1 := by
        simpa [y, upper, mul_apply, Fin.sum_univ_two] using hy'
      exact add_left_cancel (hh.trans (add_comm _ _))
    have hp := polar_action a⁻¹ z x
    rw [hbase] at hp
    rw [← hp, polar_formula]
    change d * y 1 1 + 1 * y 0 0 + 0 * y 1 0 + 0 * y 0 1 = 0
    simp [hdiag, CharTwo.add_self_eq_zero]

end ClassicalOrthogonal.FourPlusMatrix.HyperplaneFixedAux
