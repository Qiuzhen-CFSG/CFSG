module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.ThirdConjugacy.Products.Batch2

/-! Kernel-checked products for the literal third-eight conjugator.
The batches form a chain to bound the memory used by certificate builds.
ATLAS data and generation conventions are recorded in ../source/README.md. -/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.ThirdConjugacy
open Janko4 Janko4.GeneratorCertificates

set_option Elab.async false

set_option maxRecDepth 10000 in
theorem check_mask1942 : packedMul Janko4.Cardinality.KernelCount.e1Rows mask1940Rows = mask1942Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask1856 : packedMul Janko4.Cardinality.KernelCount.e6Rows mask1792Rows = mask1856Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask1872 : packedMul Janko4.Cardinality.KernelCount.e4Rows mask1856Rows = mask1872Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask640 : packedMul Janko4.Cardinality.KernelCount.e7Rows Janko4.Cardinality.KernelCount.e9Rows = mask640Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask704 : packedMul Janko4.Cardinality.KernelCount.e6Rows mask640Rows = mask704Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask736 : packedMul Janko4.Cardinality.KernelCount.e5Rows mask704Rows = mask736Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask752 : packedMul Janko4.Cardinality.KernelCount.e4Rows mask736Rows = mask752Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_mask760 : packedMul Janko4.Cardinality.KernelCount.e3Rows mask752Rows = mask760Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.ThirdConjugacy
