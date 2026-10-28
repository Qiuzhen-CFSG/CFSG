module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.Ambient.Rows

/-!
# Full 112-dimensional matrix product checks

Each check uses the proved packed multiplication algorithm and kernel reduction.
-/

public section

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.AmbientLineCertificates

open Janko4 Janko4.GeneratorCertificates Janko4.LocalStructure.SymmetricLinear
attribute [local irreducible] Janko4.modelGroup

open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators

set_option maxRecDepth 10000 in
theorem product_400 : packedMul r393 r65 = r394 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_401 : packedMul r65 r395 = r394 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_402 : packedMul r246 r65 = r396 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_403 : packedMul r65 r397 = r396 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_404 : packedMul r257 r379 = r398 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_405 : packedMul r398 r65 = r399 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_406 : packedMul r65 r400 = r399 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_407 : packedMul r268 r65 = r401 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_408 : packedMul r65 r402 = r401 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_409 : packedMul r282 r384 = r403 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_410 : packedMul r403 r65 = r404 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_411 : packedMul r65 r405 = r404 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_412 : packedMul r292 r381 = r406 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_413 : packedMul r406 r65 = r407 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_414 : packedMul r65 r408 = r407 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_415 : packedMul r303 r65 = r409 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_416 : packedMul r65 r410 = r409 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_417 : packedMul r315 r65 = r411 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_418 : packedMul r65 r412 = r411 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_419 : packedMul r326 r384 = r413 :=
  packed_of_list _ _ _ (by decide +kernel)
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.AmbientLineCertificates
