module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.ThirdConjugacy.Products.Batch1

/-! Kernel-checked products for the literal third-eight conjugator.
The batches form a chain to bound the memory used by certificate builds.
ATLAS data and generation conventions are recorded in ../source/README.md. -/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.ThirdConjugacy
open Janko4 Janko4.GeneratorCertificates

set_option Elab.async false

set_option maxRecDepth 10000 in
theorem check_mask1448 : packedMul Janko4.Cardinality.KernelCount.e3Rows mask1440Rows = mask1448Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask1452 : packedMul Janko4.Cardinality.KernelCount.e2Rows mask1448Rows = mask1452Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask1453 : packedMul Janko4.Cardinality.KernelCount.e0Rows mask1452Rows = mask1453Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask1536 : packedMul Janko4.Cardinality.KernelCount.e9Rows Janko4.Cardinality.KernelCount.e10Rows = mask1536Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask1792 : packedMul Janko4.Cardinality.KernelCount.e8Rows mask1536Rows = mask1792Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask1920 : packedMul Janko4.Cardinality.KernelCount.e7Rows mask1792Rows = mask1920Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask1936 : packedMul Janko4.Cardinality.KernelCount.e4Rows mask1920Rows = mask1936Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask1940 : packedMul Janko4.Cardinality.KernelCount.e2Rows mask1936Rows = mask1940Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.ThirdConjugacy
