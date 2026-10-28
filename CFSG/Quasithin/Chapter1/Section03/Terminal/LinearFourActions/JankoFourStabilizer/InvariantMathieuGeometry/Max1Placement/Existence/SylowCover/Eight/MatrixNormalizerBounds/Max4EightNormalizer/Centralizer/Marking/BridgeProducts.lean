module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.Marking.Data

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

theorem check_r : packedMul (NormalEight.elementRows 2) aRows = rRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem check_r2 : packedMul rRows rRows = r2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem check_r4 : packedMul r2Rows r2Rows = r4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem check_c : packedMul r4Rows rRows = cRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem check_bridge : packedMul hRows cRows = bridgeRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)


end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.MarkingCertificates
