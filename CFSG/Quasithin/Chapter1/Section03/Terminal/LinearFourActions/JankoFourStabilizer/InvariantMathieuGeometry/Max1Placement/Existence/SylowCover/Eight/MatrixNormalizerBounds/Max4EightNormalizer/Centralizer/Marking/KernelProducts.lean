module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.Marking.BridgeProducts

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

theorem check_p6144 : packedMul (factorRows 11) (factorRows 12) = p6144Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem check_p6400 : packedMul (factorRows 8) p6144Rows = p6400Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem check_p6528 : packedMul (factorRows 7) p6400Rows = p6528Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem check_p6592 : packedMul (factorRows 6) p6528Rows = p6592Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem check_p6600 : packedMul (factorRows 3) p6592Rows = p6600Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem check_p6604 : packedMul (factorRows 2) p6600Rows = p6604Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem check_p6606 : packedMul (factorRows 1) p6604Rows = p6606Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem check_p6607 : packedMul (factorRows 0) p6606Rows = p6607Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem check_q3072 : packedMul (factorRows 10) (factorRows 11) = q3072Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem check_q3328 : packedMul (factorRows 8) q3072Rows = q3328Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem check_q3392 : packedMul (factorRows 6) q3328Rows = q3392Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)

theorem check_q3400 : packedMul (factorRows 3) q3392Rows = q3400Rows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, factorRows, get_ofFn]
    decide +kernel)


end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.MarkingCertificates
