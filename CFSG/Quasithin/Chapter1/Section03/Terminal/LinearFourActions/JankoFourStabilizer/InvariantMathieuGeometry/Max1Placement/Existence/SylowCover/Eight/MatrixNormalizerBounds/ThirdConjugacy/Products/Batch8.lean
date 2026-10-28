module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.ThirdConjugacy.Products.Batch7

/-! Kernel-checked products for the literal third-eight conjugator.
The batches form a chain to bound the memory used by certificate builds.
ATLAS data and generation conventions are recorded in ../source/README.md. -/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.ThirdConjugacy
open Janko4 Janko4.GeneratorCertificates

set_option Elab.async false

set_option maxRecDepth 10000 in
theorem check_compare2Left : packedMul Janko4.LocalStructure.SymmetricLinear.NormalEight.e2Rows rightConjugatorRows = compare2LeftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_compare2Right : packedMul rightConjugatorRows mask1387Rows = compare2LeftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_compare3Left : packedMul Janko4.LocalStructure.SymmetricLinear.NormalEight.e3Rows rightConjugatorRows = compare3LeftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_compare3Right : packedMul rightConjugatorRows mask1872Rows = compare3LeftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_compare4Left : packedMul Janko4.LocalStructure.SymmetricLinear.NormalEight.e4Rows rightConjugatorRows = compare4LeftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_compare4Right : packedMul rightConjugatorRows mask765Rows = compare4LeftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_compare5Left : packedMul Janko4.LocalStructure.SymmetricLinear.NormalEight.e5Rows rightConjugatorRows = compare5LeftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_compare5Right : packedMul rightConjugatorRows mask198Rows = compare5LeftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.ThirdConjugacy
