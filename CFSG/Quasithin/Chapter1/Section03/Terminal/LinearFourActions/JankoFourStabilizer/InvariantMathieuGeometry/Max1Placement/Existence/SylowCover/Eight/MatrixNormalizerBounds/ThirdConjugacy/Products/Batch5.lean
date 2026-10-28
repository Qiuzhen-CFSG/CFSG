module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.ThirdConjugacy.Products.Batch4

/-! Kernel-checked products for the literal third-eight conjugator.
The batches form a chain to bound the memory used by certificate builds.
ATLAS data and generation conventions are recorded in ../source/README.md. -/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.ThirdConjugacy
open Janko4 Janko4.GeneratorCertificates

set_option Elab.async false

set_option maxRecDepth 10000 in
theorem check_ambientWord2 : packedMul ambientWord1Rows bInverseRows = ambientWord2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_ambientWord3 : packedMul ambientWord2Rows aRows = ambientWord3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_ambientWord4 : packedMul ambientWord3Rows bRows = ambientWord4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_ambientWord5 : packedMul ambientWord4Rows bRows = ambientWord5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_ambientWord6 : packedMul ambientWord5Rows bRows = ambientWord6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_ambientWord7 : packedMul ambientWord6Rows aRows = ambientWord7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_ambientWord8 : packedMul ambientWord7Rows bInverseRows = ambientWord8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_ambientWord9 : packedMul ambientWord8Rows aRows = ambientWord9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.ThirdConjugacy
