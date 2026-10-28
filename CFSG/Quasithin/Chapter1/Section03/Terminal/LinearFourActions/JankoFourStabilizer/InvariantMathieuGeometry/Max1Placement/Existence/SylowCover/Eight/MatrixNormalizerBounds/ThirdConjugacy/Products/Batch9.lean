module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.ThirdConjugacy.Products.Batch8

/-! Kernel-checked products for the literal third-eight conjugator.
The batches form a chain to bound the memory used by certificate builds.
ATLAS data and generation conventions are recorded in ../source/README.md. -/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.ThirdConjugacy
open Janko4 Janko4.GeneratorCertificates

set_option Elab.async false

set_option maxRecDepth 10000 in
theorem check_compare6Left : packedMul Janko4.LocalStructure.SymmetricLinear.NormalEight.e6Rows rightConjugatorRows = compare6LeftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_compare6Right : packedMul rightConjugatorRows mask571Rows = compare6LeftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_compare7Left : packedMul Janko4.LocalStructure.SymmetricLinear.NormalEight.e7Rows rightConjugatorRows = compare7LeftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem check_compare7Right : packedMul rightConjugatorRows mask1942Rows = compare7LeftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.ThirdConjugacy
