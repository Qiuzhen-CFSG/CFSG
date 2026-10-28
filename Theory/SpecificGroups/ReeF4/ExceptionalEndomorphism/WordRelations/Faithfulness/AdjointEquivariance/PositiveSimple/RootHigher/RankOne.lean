module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootHigher.IntegralReduction
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Relations

/-!
# The rank-one quadratic comparisons

For the positive simple root the second adjoint divided power is zero. For
its negative it is minus the positive simple operator, while the second
vector column gives the positive operator. Thus the required integral sign
is respectively `1` and `-1`.

For the negative-root identity, expand the simple sl₂ relation
`[H,E] = 2E` and cancel `2` over the integers before specialization. The
vector-column calculation uses the root-string formula of
`IntegralGeckConstruction`. The simple sl₂ relation is Geck's Lemma 3.3(a),
formalized in `GeckConstruction.Relations`.
-/

public section

open scoped Matrix
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
noncomputable section
lemma integralQuadraticOperator_negative_simple (i : typeF4RootPairing_base.support) :
    letI := typeF4RootPairing.indexNeg
    integralQuadraticOperator i (-i : typeF4Roots) = -eMatrix (P := typeF4RootPairing) i := by
  let := typeF4RootPairing.indexNeg
  let E := eMatrix (P := typeF4RootPairing) i
  let F := fMatrix (P := typeF4RootPairing) i
  let B := eDividedPower (P := typeF4RootPairing) i 2
  have hHE : (E * F - F * E) * E - E * (E * F - F * E) = (2 : ℤ) • E := by
    apply Matrix.map_injective (FaithfulSMul.algebraMap_injective ℤ ℝ)
    dsimp only [E, F]
    simp only [Matrix.map_sub _ (map_sub _), Matrix.map_mul,
      Matrix.map_smul _ _ (map_zsmul _ _), map_eMatrix, map_fMatrix]
    have h := RootPairing.GeckConstruction.lie_h_e (P := typeF4RootPairing) i i
    rw [← RootPairing.GeckConstruction.lie_e_f_same i] at h
    simpa only [Ring.lie_def, RootPairing.Base.cartanMatrix_apply_same] using h
  have hEE : E * E = (2 : ℤ) • B := by
    have h := eDividedPower_mul (P := typeF4RootPairing) i 1 1
    rw [← Nat.cast_smul_eq_nsmul ℤ] at h
    exact h
  have hJ : (2 : ℤ) • (B * F - E * F * E + F * B) = -((2 : ℤ) • E) := by
    calc
      _ = (E * E) * F - (E * F * E + E * F * E) + F * (E * E) := by
        rw [hEE]
        simp only [smul_add, smul_sub, two_smul, add_mul, mul_add]
      _ = -((E * F - F * E) * E - E * (E * F - F * E)) := by noncomm_ring
      _ = _ := by rw [hHE]
  change eDividedPower (P := typeF4RootPairing) i 2 *
      rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-i : typeF4Roots) -
    eMatrix i * rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-i : typeF4Roots) * eMatrix i +
      rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-i : typeF4Roots) * eDividedPower i 2 = _
  rw [rootOperator_neg_simple]
  change B * F - E * F * E + F * B = -E
  ext x y
  have hxy := congrFun (congrFun hJ x) y
  simp only [Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul] at hxy ⊢
  linarith

lemma integralQuadraticColumn_negative_simple (i : typeF4RootPairing_base.support) :
    letI := typeF4RootPairing.indexNeg
    integralQuadraticColumn i (-i : typeF4Roots) = eMatrix (P := typeF4RootPairing) i := by
  classical
  let := typeF4RootPairing.indexNeg
  have htop : typeF4RootPairing.chainTopCoeff i i = 0 :=
    typeF4RootPairing.chainTopCoeff_of_not_linearIndependent (by
      simp_rw [LinearIndependent.pair_iff, not_forall]
      exact ⟨1, -1, by simp, by simp⟩)
  have hc : eDividedPower (P := typeF4RootPairing) i 2 *ᵥ v (b := typeF4RootPairing_base) (-i : typeF4Roots) =
      v (b := typeF4RootPairing_base) (i : typeF4Roots) := by
    simpa [htop] using eDividedPower_add_two_mulVec_v (P := typeF4RootPairing)
      (i := i) (j := (-i : typeF4Roots)) (n := 0) (k := (i : typeF4Roots)) (by
        simp only [RootPairing.indexNeg_neg, typeF4RootPairing.root_reflectionPerm,
          typeF4RootPairing.reflection_apply_self, Nat.zero_add]
        module)
  have hcol (s : typeF4Roots) :
      eDividedPower (P := typeF4RootPairing) i 2 (Sum.inr s) (Sum.inr (-i : typeF4Roots)) =
        if s = i then (1 : ℤ) else 0 := by
    have h := congrFun hc (Sum.inr s)
    simpa [v, Pi.single_apply, eq_comm] using h
  simp only [integralQuadraticColumn, hcol, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  exact rootOperator_simple i

lemma integralQuadraticComparison_negative_simple (i : typeF4RootPairing_base.support) :
    letI := typeF4RootPairing.indexNeg
    ∃ ε : ℤ, ε ^ 2 = 1 ∧ integralQuadraticOperator i (-i : typeF4Roots) =
      ε • integralQuadraticColumn i (-i : typeF4Roots) := by
  let := typeF4RootPairing.indexNeg
  refine ⟨-1, by norm_num, ?_⟩
  rw [integralQuadraticOperator_negative_simple, integralQuadraticColumn_negative_simple,
    neg_one_smul]

lemma integralQuadraticOperator_simple (i : typeF4RootPairing_base.support) :
    integralQuadraticOperator i (i : typeF4Roots) = 0 := by
  have hroot : F4Chevalley.integralOperators.rootOperator i = eMatrix (P := typeF4RootPairing) i :=
    rootOperator_simple i
  have hBE : eDividedPower (P := typeF4RootPairing) i 2 * eMatrix i = 0 := by
    rw [← eDividedPower_one, eDividedPower_mul, eDividedPower_three, smul_zero]
  have hEB : eMatrix (P := typeF4RootPairing) i * eDividedPower i 2 = 0 := by
    rw [← eDividedPower_one, eDividedPower_mul, eDividedPower_three, smul_zero]
  have h3 := eMatrix_pow_eq_factorial_smul (P := typeF4RootPairing) i 3
  rw [eDividedPower_three, smul_zero] at h3
  simp only [integralQuadraticOperator, hroot, hBE, hEB, ← pow_succ, ← pow_two,
    h3, sub_zero, add_zero]

lemma integralQuadraticColumn_simple (i : typeF4RootPairing_base.support) :
    integralQuadraticColumn i (i : typeF4Roots) = 0 := by
  classical
  have he (s : typeF4Roots) : typeF4RootPairing.root s ≠
      typeF4RootPairing.root i + (2 : ℕ) • typeF4RootPairing.root i := by
    intro h
    have : (3 : ℕ).AtLeastTwo := ⟨by omega⟩
    apply typeF4RootPairing.nsmul_notMem_range_root (n := 3) (i := i)
    exact ⟨s, by rw [h]; module⟩
  unfold integralQuadraticColumn
  apply Finset.sum_eq_zero
  intro s _
  simp only [eDividedPower, Matrix.of_apply, if_neg (he s), zero_smul]

lemma integralQuadraticComparison_simple (i : typeF4RootPairing_base.support) :
    ∃ ε : ℤ, ε ^ 2 = 1 ∧ integralQuadraticOperator i (i : typeF4Roots) =
      ε • integralQuadraticColumn i (i : typeF4Roots) := by
  exact ⟨1, by norm_num, by rw [integralQuadraticOperator_simple,
    integralQuadraticColumn_simple, smul_zero]⟩
end
end ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
