module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.ThirdConjugacy.Products.Batch0

/-! Kernel-checked products for the literal third-eight conjugator.
The batches form a chain to bound the memory used by certificate builds.
ATLAS data and generation conventions are recorded in ../source/README.md. -/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.ThirdConjugacy
open Janko4 Janko4.GeneratorCertificates

set_option Elab.async false

set_option maxRecDepth 10000 in
theorem check_mask1384 : packedMul Janko4.Cardinality.KernelCount.e3Rows mask1376Rows = mask1384Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask1386 : packedMul Janko4.Cardinality.KernelCount.e1Rows mask1384Rows = mask1386Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask1387 : packedMul Janko4.Cardinality.KernelCount.e0Rows mask1386Rows = mask1387Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask192 : packedMul Janko4.Cardinality.KernelCount.e6Rows Janko4.Cardinality.KernelCount.e7Rows = mask192Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask196 : packedMul Janko4.Cardinality.KernelCount.e2Rows mask192Rows = mask196Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask198 : packedMul Janko4.Cardinality.KernelCount.e1Rows mask196Rows = mask198Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask1408 : packedMul Janko4.Cardinality.KernelCount.e7Rows mask1280Rows = mask1408Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask1440 : packedMul Janko4.Cardinality.KernelCount.e5Rows mask1408Rows = mask1440Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.ThirdConjugacy
