module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.ThirdConjugacy.Data

/-! Kernel-checked products for the literal third-eight conjugator.
The batches form a chain to bound the memory used by certificate builds.
ATLAS data and generation conventions are recorded in ../source/README.md. -/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.ThirdConjugacy
open Janko4 Janko4.GeneratorCertificates

set_option Elab.async false

set_option maxRecDepth 10000 in
theorem check_mask544 : packedMul Janko4.Cardinality.KernelCount.e5Rows Janko4.Cardinality.KernelCount.e9Rows = mask544Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask560 : packedMul Janko4.Cardinality.KernelCount.e4Rows mask544Rows = mask560Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask568 : packedMul Janko4.Cardinality.KernelCount.e3Rows mask560Rows = mask568Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask570 : packedMul Janko4.Cardinality.KernelCount.e1Rows mask568Rows = mask570Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask571 : packedMul Janko4.Cardinality.KernelCount.e0Rows mask570Rows = mask571Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask1280 : packedMul Janko4.Cardinality.KernelCount.e8Rows Janko4.Cardinality.KernelCount.e10Rows = mask1280Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask1344 : packedMul Janko4.Cardinality.KernelCount.e6Rows mask1280Rows = mask1344Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask1376 : packedMul Janko4.Cardinality.KernelCount.e5Rows mask1344Rows = mask1376Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.ThirdConjugacy
