module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.Marking.KernelProducts

/-!
# Kernel-checked products for the max4-eight marking

The module chain and sequential elaboration bound concurrent memory use.
Each identity checks all 112 rows using the proved packed multiplication
algorithm. Source attribution and the exact word conventions are in Data.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.MarkingCertificates
open Janko4 Janko4.GeneratorCertificates Janko4.LocalStructure.SymmetricLinear
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound.KernelSeparation

set_option Elab.async false

theorem check_intertwine1 : packedMul bridgeRows (NormalEight.elementRows 1) = intertwine1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem check_intertwine1_right : packedMul p6607Rows bridgeRows = intertwine1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem check_intertwine2 : packedMul bridgeRows (NormalEight.elementRows 2) = intertwine2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem check_intertwine2_right : packedMul tRows bridgeRows = intertwine2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem check_intertwine3 : packedMul bridgeRows (NormalEight.elementRows 3) = intertwine3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem check_intertwine3_right : packedMul q3400Rows bridgeRows = intertwine3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)


end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.MarkingCertificates
