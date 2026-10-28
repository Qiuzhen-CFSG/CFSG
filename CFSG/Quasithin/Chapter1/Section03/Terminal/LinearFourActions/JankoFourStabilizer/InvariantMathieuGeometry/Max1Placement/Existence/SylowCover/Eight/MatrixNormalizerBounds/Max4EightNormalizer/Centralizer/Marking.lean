module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.Definitions
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.Marking.Evaluations

/-!
# The literal max4-eight marking in the original ATLAS max2 subgroup

Left conjugation by the specified bridge carries the three basis involutions
respectively to masks 6607, t, and 3400. The proof checks the equivalent
intertwining identities bridge * element = target * bridge on every matrix row,
then uses faithfulness and cancellation in the original matrix group.
This supplies the Marking premise of Max4EightCentralizer.centralizer_card_le;
the independent pair-orbit certificate remains with the final assembly owner.

Source: retained ATLAS J4G1-f2r112B0, J4G1-max4W1 and J4G1-max2W1 data,
with original attribution and license in their source directories;
Kleidman–Wilson (1988), pp.484–510; Aschbacher–Smith A.3.12, pp.47–48.
-/

public section
set_option backward.isDefEq.respectTransparency true
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer
open Janko4 Janko4.GeneratorCertificates Janko4.LocalStructure.SymmetricLinear
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open MarkingCertificates

attribute [local irreducible] decodeRows toMatrix

private theorem conjugation_of_intertwining {x y : Model} {xs ys : Vector ℕ 112}
    (hx : toMatrix x = decodeRows xs) (hy : toMatrix y = decodeRows ys)
    (hc : packedMul bridgeRows xs = packedMul ys bridgeRows) :
    (MulAut.conj bridge) x = y := by
  have he : bridge * x = y * bridge := by
    apply toMatrix_injective
    simpa only [map_mul, eval_bridge, hx, hy, ← decode_packedMul] using
      congrArg decodeRows hc
  change bridge * x * bridge⁻¹ = y
  rw [he, mul_assoc, mul_inv_cancel, mul_one]

/-- The three specified max4 basis elements have their literal max2 markings. -/
theorem marking : Marking := by
  refine ⟨?_, ?_, ?_⟩
  · exact conjugation_of_intertwining (NormalEight.matrix_element 1) eval_sourceP
      (check_intertwine1.trans check_intertwine1_right.symm)
  · exact conjugation_of_intertwining (NormalEight.matrix_element 2) eval_t
      (check_intertwine2.trans check_intertwine2_right.symm)
  · exact conjugation_of_intertwining (NormalEight.matrix_element 3) eval_sourceQ
      (check_intertwine3.trans check_intertwine3_right.symm)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer
