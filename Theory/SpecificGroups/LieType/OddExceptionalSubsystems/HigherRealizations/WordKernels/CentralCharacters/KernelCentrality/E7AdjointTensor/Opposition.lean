module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.E7AdjointTensor.Model
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.CoverCenter.Equivariance.Opposition.IntegralWords

/-!
# Signed opposition covariance of the integral E7 adjoint map

The opposition matrix fixes Cartan coordinates and exchanges opposite root
coordinates. On Cartan operators it reverses the raising/lowering commutator.
For each positive root, the positive and negative operators use the same
canonical Tits word. Its integral opposition correction is exactly the product
of its two carrier signs; the corrected `rootOperatorOrientation` cancels that
product and supplies the minus sign.

Thus the literal fixed integral map satisfies `D(Ωv) = -(Ω * D(v) * Ω)`.
The final application discharges the opposition premise of
`negative_integral_commutators_of_positive_and_opposition`; the positive identity
is proved in `PositiveCommutators`, and `Curves` consumes both identities.

Adapted from the checked F4 `CoverCenter.Equivariance.Opposition` proof.
Sources: `IntegralGeckConstruction`, `IntegralAllRootOperators`,
`IntegralChevalleyOperatorOrientation`, and GLS3 §§2.2–2.6.
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
local instance rootsInOpposition : Fintype typeE7Roots := Fintype.ofFinite _

private lemma integralCoordinateOperator_opposite_pos
    (r : typeE7Roots) (hr : typeE7RootPairing_base.IsPos r) :
    let := typeE7RootPairing.indexNeg
    integralCoordinateOperator (Sum.inr (-r)) =
      -(omegaMatrix * integralCoordinateOperator (Sum.inr r) * omegaMatrix) := by
  let := typeE7RootPairing.indexNeg
  dsimp only
  have hn : ¬typeE7RootPairing_base.IsPos (-r) := by
    rw [RootPairing.Base.IsPos.neg_iff_not]
    exact not_not_intro hr
  let w := (rootRoute (P := typeE7RootPairing) (b := typeE7RootPairing_base) r).word
  let i := (rootRoute (P := typeE7RootPairing) (b := typeE7RootPairing_base) r).simple
  have hp : rootOperatorOrientation r = titsWordSign w i * simpleOperatorOrientation i := by
    rw [rootOperatorOrientation, if_pos hr]
    rfl
  have hm : rootOperatorOrientation (-r) = titsWordSign w (-i) * -simpleOperatorOrientation i := by
    rw [rootOperatorOrientation, if_neg hn, neg_neg]
    rfl
  simp only [integralCoordinateOperator, hp, hm, Matrix.mul_smul, Matrix.smul_mul]
  rw [rootOperator_neg_of_pos r hr, rootOperator_of_pos r hr,
    omegaMatrix_conj_transported_eMatrix]
  simp only [smul_smul, ← neg_smul, titsWordOppositionSign]
  congr 1
  change titsWordSign w (-i) * -simpleOperatorOrientation i =
    -(titsWordSign w i * simpleOperatorOrientation i *
      (titsWordSign w i * titsWordSign w (-i)))
  calc
    _ = -(1 * (titsWordSign w (-i) * simpleOperatorOrientation i)) := by ring
    _ = -((titsWordSign w i * titsWordSign w i) *
        (titsWordSign w (-i) * simpleOperatorOrientation i)) := by
      rw [titsWordSign_mul_self_opposition]
    _ = _ := by ring

/-- Opposition exchanges the signed operators at every pair of opposite roots,
with the integral minus sign. -/
lemma integralCoordinateOperator_opposite (r : typeE7Roots) :
    let := typeE7RootPairing.indexNeg
    integralCoordinateOperator (Sum.inr (-r)) =
      -(omegaMatrix * integralCoordinateOperator (Sum.inr r) * omegaMatrix) := by
  let := typeE7RootPairing.indexNeg
  dsimp only
  by_cases hr : typeE7RootPairing_base.IsPos r
  · exact integralCoordinateOperator_opposite_pos r hr
  · have hn : typeE7RootPairing_base.IsPos (-r) :=
      (RootPairing.Base.IsPos.neg_iff_not _ _).mpr hr
    have h := integralCoordinateOperator_opposite_pos (-r) hn
    simp only [neg_neg] at h
    rw [h]
    simp only [mul_neg, neg_mul, neg_neg]
    symm
    calc
      _ = (omegaMatrix * omegaMatrix) * integralCoordinateOperator (Sum.inr (-r)) *
          (omegaMatrix * omegaMatrix) := by noncomm_ring
      _ = _ := by rw [omegaMatrix_sq, one_mul, mul_one]

/-- The Cartan coordinate is fixed on the carrier and negated by conjugation
on its signed commutator operator. -/
lemma integralCoordinateOperator_cartan_opposition (i : typeE7RootPairing_base.support) :
    integralCoordinateOperator (Sum.inl i) =
      -(omegaMatrix * integralCoordinateOperator (Sum.inl i) * omegaMatrix) := by
  let O := omegaMatrix (P := typeE7RootPairing) (b := typeE7RootPairing_base)
  let E := eMatrix (P := typeE7RootPairing) i
  let F := fMatrix (P := typeE7RootPairing) i
  have he : O * E = F * O := omegaMatrix_mul_eMatrix i
  have hf : O * F = E * O := omegaMatrix_mul_fMatrix i
  have hoo : O * O = 1 := omegaMatrix_sq
  have hcomm : O * (E * F - F * E) * O = -(E * F - F * E) := by
    calc
      _ = (O * E) * F * O - (O * F) * E * O := by noncomm_ring
      _ = F * (O * F) * O - E * (O * E) * O := by
        conv_lhs => rw [he, hf]
        noncomm_ring
      _ = F * E * (O * O) - E * F * (O * O) := by
        conv_lhs => rw [hf, he]
        noncomm_ring
      _ = _ := by rw [hoo, mul_one, mul_one]; abel
  change -simpleOperatorOrientation i • (E * F - F * E) =
    -(O * (-simpleOperatorOrientation i • (E * F - F * E)) * O)
  rw [Matrix.mul_smul, Matrix.smul_mul, hcomm, smul_neg, neg_neg]

/-- The fixed integral signed adjoint map is covariant under opposition.
This discharges the opposition premise of the negative-commutator transfer. -/
theorem integral_opposition_covariance : IntegralOppositionCovariance := by
  have hb (j : Coordinate) :
      integralAdjointMap (omegaMatrix *ᵥ Pi.single j 1) =
        -(omegaMatrix * integralAdjointMap (Pi.single j 1) * omegaMatrix) := by
    rcases j with i | r
    · change integralAdjointMap (omegaMatrix *ᵥ u i) = _
      rw [omegaMatrix_mulVec_u, integralAdjointMap_single]
      exact integralCoordinateOperator_cartan_opposition i
    · let := typeE7RootPairing.indexNeg
      change integralAdjointMap (omegaMatrix *ᵥ v r) = _
      rw [omegaMatrix_mulVec_v, integralAdjointMap_single, integralAdjointMap_single]
      exact integralCoordinateOperator_opposite r
  intro x
  have hx : x = ∑ j, x j • Pi.single j 1 := by
    ext k
    simp [Pi.single_apply]
  rw [hx]
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, map_sum, map_smul,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    ← Finset.sum_neg_distrib, ← smul_neg]
  exact Finset.sum_congr rfl (fun j _ => congrArg (fun A => x j • A) (hb j))

/-- The actual negative infinitesimal identity now needs only its independent
positive-commutator premise. -/
theorem negative_integral_commutators_of_positive
    (hE : PositiveIntegralCommutators) : NegativeIntegralCommutators :=
  negative_integral_commutators_of_positive_and_opposition hE integral_opposition_covariance

end TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E7AdjointTensor
