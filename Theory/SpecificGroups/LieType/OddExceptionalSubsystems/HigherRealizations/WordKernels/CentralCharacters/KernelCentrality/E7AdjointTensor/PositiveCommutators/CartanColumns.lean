module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.E7AdjointTensor.Model
public import Theory.AlgebraicGroup.RootSystems.IntegralChevalleyBrackets

/-!
# Signed Cartan columns of the integral E7 adjoint operators

The bipartite simple orientations turn the absolute Cartan entries in Geck's
matrices into signed pairings. This proves the positive-simple commutator on
Cartan and opposite-simple coordinates. Transporting the same column formula
along a Tits word proves `D(r) u_j = ε_j ⟨r, α_j∨⟩ v_r` for the literal
canonical root operator, for both polarities. The Tits carrier signs occur
twice and cancel; the negative-simple seed retains its minus sign.

The all-root column formula determines the signed root-sum commutator
coefficient in `PositiveCommutators.RootSums`. Sources: the integral Geck
root-string and Tits formulas in `IntegralGeckConstruction`, the bipartite
normalization in `IntegralChevalleyOperatorOrientation`, and the Chevalley
lattice conventions of GLS3 §§2.2–2.6.
Adapted from the checked F4 `CoverCenter.Equivariance.PositiveCommutators.CartanColumns` proof.
-/

@[expose] public section

open scoped Matrix Classical
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Theory.AlgebraicGroup
open ReeF4.WordRelations.Faithfulness
noncomputable section
namespace TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E7AdjointTensor

attribute [local instance] Classical.decEq
local instance rootsInCartanColumns : Fintype typeE7Roots := Fintype.ofFinite _

lemma integralCoordinateOperator_simple (i : typeE7RootPairing_base.support) :
    integralCoordinateOperator (Sum.inr (i : typeE7Roots)) =
      simpleOperatorOrientation (b := typeE7RootPairing_base) i •
        eMatrix (P := typeE7RootPairing) i := by
  simp only [integralCoordinateOperator, rootOperatorOrientation_simple, rootOperator_simple]

lemma integralCoordinateOperator_neg_simple (i : typeE7RootPairing_base.support) :
    let := typeE7RootPairing.indexNeg
    integralCoordinateOperator (Sum.inr (-i : typeE7Roots)) =
      -simpleOperatorOrientation (b := typeE7RootPairing_base) i •
        fMatrix (P := typeE7RootPairing) i := by
  let := typeE7RootPairing.indexNeg
  simp only [integralCoordinateOperator, rootOperatorOrientation_neg_simple,
    rootOperator_neg_simple]

lemma simple_orientation_abs_cartan (i j : typeE7RootPairing_base.support) :
    |typeE7RootPairing_base.cartanMatrix i j| *
        simpleOperatorOrientation (b := typeE7RootPairing_base) i =
      simpleOperatorOrientation (b := typeE7RootPairing_base) j *
        typeE7RootPairing_base.cartanMatrix i j := by
  by_cases hij : i = j
  · subst j
    simp [mul_comm]
  by_cases ha : typeE7RootPairing_base.cartanMatrix i j = 0
  · simp [ha]
  have hs := simpleOperatorOrientation_mul_eq_neg_one_of_cartan_ne_zero i j hij ha
  have hj : simpleOperatorOrientation (b := typeE7RootPairing_base) j =
      -simpleOperatorOrientation (b := typeE7RootPairing_base) i := by
    calc
      _ = (simpleOperatorOrientation (b := typeE7RootPairing_base) i *
          simpleOperatorOrientation (b := typeE7RootPairing_base) i) *
            simpleOperatorOrientation (b := typeE7RootPairing_base) j := by
        rw [simpleOperatorOrientation_sq, one_mul]
      _ = _ := by rw [mul_assoc, hs, mul_neg_one]
  rw [abs_of_nonpos (typeE7RootPairing_base.cartanMatrix_le_zero_of_ne i j hij), hj]
  ring

private lemma integralCartan_e (i j : typeE7RootPairing_base.support) :
    (eMatrix (P := typeE7RootPairing) j * fMatrix j - fMatrix j * eMatrix j) *
        eMatrix i -
      eMatrix i * (eMatrix j * fMatrix j - fMatrix j * eMatrix j) =
        typeE7RootPairing_base.cartanMatrix i j • eMatrix i := by
  apply Matrix.map_injective (FaithfulSMul.algebraMap_injective ℤ ℝ)
  dsimp only
  simp only [Matrix.map_sub _ (map_sub _), Matrix.map_mul,
    Matrix.map_smul _ _ (map_zsmul _ _), map_eMatrix, map_fMatrix]
  have h := RootPairing.GeckConstruction.lie_h_e (P := typeE7RootPairing) i j
  rw [← RootPairing.GeckConstruction.lie_e_f_same j] at h
  exact h

/-- Infinitesimal intertwining on every Cartan coordinate. -/
lemma positive_integral_commutator_cartan (i j : typeE7RootPairing_base.support) :
    integralAdjointMap (eMatrix (P := typeE7RootPairing) i *ᵥ u j) =
      eMatrix i * integralCoordinateOperator (Sum.inl j) -
        integralCoordinateOperator (Sum.inl j) * eMatrix i := by
  rw [eMatrix_mulVec_u, map_smul, integralAdjointMap_single,
    integralCoordinateOperator_simple]
  change _ = eMatrix i * (-simpleOperatorOrientation (b := typeE7RootPairing_base) j •
      (eMatrix j * fMatrix j - fMatrix j * eMatrix j)) -
    (-simpleOperatorOrientation (b := typeE7RootPairing_base) j •
      (eMatrix j * fMatrix j - fMatrix j * eMatrix j)) * eMatrix i
  rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, ← neg_sub
    ((eMatrix j * fMatrix j - fMatrix j * eMatrix j) * eMatrix i)
    (eMatrix i * (eMatrix j * fMatrix j - fMatrix j * eMatrix j)),
    integralCartan_e]
  simp only [smul_smul, smul_neg, neg_mul, neg_smul, neg_neg]
  rw [simple_orientation_abs_cartan]

/-- Infinitesimal intertwining on the opposite-simple root coordinate. -/
lemma positive_integral_commutator_opposite (i : typeE7RootPairing_base.support) :
    let := typeE7RootPairing.indexNeg
    integralAdjointMap (eMatrix (P := typeE7RootPairing) i *ᵥ v (b := typeE7RootPairing_base) (-i)) =
      eMatrix i * integralCoordinateOperator (Sum.inr (-i : typeE7Roots)) -
        integralCoordinateOperator (Sum.inr (-i : typeE7Roots)) * eMatrix i := by
  let := typeE7RootPairing.indexNeg
  dsimp only
  rw [eMatrix_mulVec_v_neg, integralAdjointMap_single, integralCoordinateOperator_neg_simple]
  simp only [integralCoordinateOperator, Matrix.mul_smul, Matrix.smul_mul, smul_sub]

private lemma pairingIn_reflect (i j : typeE7RootPairing_base.support) (r : typeE7Roots) :
    typeE7RootPairing.pairingIn ℤ (typeE7RootPairing.reflectionPerm i r) j =
      typeE7RootPairing.pairingIn ℤ r j - typeE7RootPairing_base.cartanMatrix i j *
        typeE7RootPairing.pairingIn ℤ r i := by
  apply FaithfulSMul.algebraMap_injective ℤ ℝ
  simp only [map_sub, map_mul, RootPairing.algebraMap_pairingIn,
    RootPairing.Base.algebraMap_cartanMatrixIn_apply]
  change typeE7RootPairing.toLinearMap
    (typeE7RootPairing.root (typeE7RootPairing.reflectionPerm i r))
      (typeE7RootPairing.coroot j) = _
  rw [typeE7RootPairing.root_reflectionPerm, typeE7RootPairing.reflection_apply_root]
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply]
  rw [typeE7RootPairing.root_coroot_eq_pairing, typeE7RootPairing.root_coroot_eq_pairing]
  ring

private lemma titsLiftInv_cartan (i j : typeE7RootPairing_base.support) :
    titsLiftInv (P := typeE7RootPairing) i *ᵥ u j =
      u j - |typeE7RootPairing_base.cartanMatrix i j| • u i := by
  have hfix : titsLift (P := typeE7RootPairing) i *ᵥ (titsLift i *ᵥ u j) = u j := by
    rw [titsLift_mulVec_u, Matrix.mulVec_sub, Matrix.mulVec_smul,
      titsLift_mulVec_u, titsLift_mulVec_u]
    have hii : |typeE7RootPairing_base.cartanMatrix i i| = 2 := by simp
    rw [hii]
    module
  calc
    _ = titsLiftInv i *ᵥ (titsLift i *ᵥ (titsLift i *ᵥ u j)) := by rw [hfix]
    _ = titsLift i *ᵥ u j := by
      rw [Matrix.mulVec_mulVec, titsLift_inv_mul, Matrix.one_mulVec]
    _ = _ := titsLift_mulVec_u i j

private lemma transported_cartan_columns (r : typeE7Roots)
    (A : Matrix Coordinate Coordinate ℤ)
    (hA : ∀ j : typeE7RootPairing_base.support, A *ᵥ u j =
      (simpleOperatorOrientation (b := typeE7RootPairing_base) j *
        typeE7RootPairing.pairingIn ℤ r j) • v (b := typeE7RootPairing_base) r)
    (w : List typeE7RootPairing_base.support) (j : typeE7RootPairing_base.support) :
    transportedMatrix (P := typeE7RootPairing) w A *ᵥ u j =
      (titsWordSign w r * simpleOperatorOrientation (b := typeE7RootPairing_base) j *
        typeE7RootPairing.pairingIn ℤ (reflectionWord w r) j) •
          v (b := typeE7RootPairing_base) (reflectionWord w r) := by
  induction w generalizing j with
  | nil => simpa [transportedMatrix, titsWord, titsWordSign, reflectionWord] using hA j
  | cons i w ih =>
      have hcons : transportedMatrix (P := typeE7RootPairing) (i :: w) A =
          titsLift i * transportedMatrix w A * titsLiftInv i := by
        simp only [transportedMatrix, titsWord, titsWordInv_cons, mul_assoc]
      rw [hcons, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, titsLiftInv_cartan,
        Matrix.mulVec_sub, Matrix.mulVec_smul, ih j, ih i,
        Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, titsLift_mulVec_v]
      simp only [Matrix.mulVec_smul, titsLift_mulVec_v, smul_smul, ← sub_smul,
        reflectionWord, titsWordSign, pairingIn_reflect]
      congr 1
      have h := simple_orientation_abs_cartan i j
      linear_combination -(titsWordSign w r *
        (-1 : ℤ) ^ typeE7RootPairing.chainBotCoeff i (reflectionWord w r) *
          typeE7RootPairing.pairingIn ℤ (reflectionWord w r) i) * h

private lemma signed_e_cartan (i j : typeE7RootPairing_base.support) :
    (simpleOperatorOrientation (b := typeE7RootPairing_base) i •
        eMatrix (P := typeE7RootPairing) i) *ᵥ u j =
      (simpleOperatorOrientation (b := typeE7RootPairing_base) j *
        typeE7RootPairing.pairingIn ℤ i j) • v (b := typeE7RootPairing_base) i := by
  rw [Matrix.smul_mulVec, eMatrix_mulVec_u, smul_smul, mul_comm,
    simple_orientation_abs_cartan]
  rfl

private lemma signed_f_cartan (i j : typeE7RootPairing_base.support) :
    let := typeE7RootPairing.indexNeg
    (-simpleOperatorOrientation (b := typeE7RootPairing_base) i •
        fMatrix (P := typeE7RootPairing) i) *ᵥ u j =
      (simpleOperatorOrientation (b := typeE7RootPairing_base) j *
        typeE7RootPairing.pairingIn ℤ (-i : typeE7Roots) j) •
          v (b := typeE7RootPairing_base) (-i : typeE7Roots) := by
  let := typeE7RootPairing.indexNeg
  dsimp only
  rw [Matrix.smul_mulVec, fMatrix_mulVec_u, smul_smul, neg_mul, mul_comm,
    simple_orientation_abs_cartan]
  simp only [RootPairing.indexNeg_neg, RootPairing.pairingIn_reflectionPerm_self_left,
    mul_neg]
  rfl

/-- Exact signed Cartan columns of the canonical all-root operators. -/
lemma integralCoordinateOperator_cartan_column (r : typeE7Roots)
    (j : typeE7RootPairing_base.support) :
    integralCoordinateOperator (Sum.inr r) *ᵥ u j =
      (simpleOperatorOrientation (b := typeE7RootPairing_base) j *
        typeE7RootPairing.pairingIn ℤ r j) • v (b := typeE7RootPairing_base) r := by
  let := typeE7RootPairing.indexNeg
  by_cases hr : typeE7RootPairing_base.IsPos r
  · let z := rootRoute (P := typeE7RootPairing) (b := typeE7RootPairing_base) r
    have ht : integralCoordinateOperator (Sum.inr r) =
        titsWordSign z.word z.simple • transportedMatrix z.word
          (simpleOperatorOrientation (b := typeE7RootPairing_base) z.simple • eMatrix z.simple) := by
      simp only [integralCoordinateOperator, rootOperator_of_pos r hr,
        rootOperatorOrientation, if_pos hr, simpleRouteOperatorOrientation,
        if_true, signedSimpleOperatorOrientation_true,
        transportedMatrix, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
      rfl
    rw [ht, Matrix.smul_mulVec, transported_cartan_columns _ _ (signed_e_cartan z.simple)]
    simp only [smul_smul, ← mul_assoc, titsWordSign_mul_self, one_mul, z.target]
  · have hn : typeE7RootPairing_base.IsPos (-r) :=
      (RootPairing.Base.IsPos.neg_iff_not _ _).mpr hr
    let z := rootRoute (P := typeE7RootPairing) (b := typeE7RootPairing_base) (-r)
    have he := rootOperator_neg_of_pos (P := typeE7RootPairing)
      (b := typeE7RootPairing_base) (-r) hn
    simp only [neg_neg] at he
    have ht : integralCoordinateOperator (Sum.inr r) =
        titsWordSign z.word (-z.simple : typeE7Roots) • transportedMatrix z.word
          (-simpleOperatorOrientation (b := typeE7RootPairing_base) z.simple • fMatrix z.simple) := by
      simp only [integralCoordinateOperator, he,
        rootOperatorOrientation, if_neg hr, simpleRouteOperatorOrientation,
        Bool.false_eq_true, if_false, signedSimpleOperatorOrientation_false,
        transportedMatrix, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
      rfl
    rw [ht, Matrix.smul_mulVec,
      transported_cartan_columns _ _ (signed_f_cartan z.simple)]
    simp only [smul_smul, ← mul_assoc, titsWordSign_mul_self, one_mul,
      reflectionWord_neg, z.target, neg_neg]

end TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E7AdjointTensor
