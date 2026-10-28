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
theorem product_60 : packedMul r56 r54 = r58 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_61 : packedMul r58 r57 = r59 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_62 : packedMul r59 r55 = r60 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_63 : packedMul r60 r57 = r61 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_64 : packedMul r61 r55 = r62 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_65 : packedMul r62 r57 = r63 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_66 : packedMul r63 r55 = r64 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_67 : packedMul r53 r64 = r65 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_68 : packedMul r57 r54 = r66 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_69 : packedMul r66 r57 = r67 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_70 : packedMul r67 r55 = r68 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_71 : packedMul r68 r57 = r69 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_72 : packedMul r69 r55 = r70 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_73 : packedMul r70 r57 = r71 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_74 : packedMul r71 r55 = r72 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_75 : packedMul r72 r57 = r73 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_76 : packedMul r73 r54 = r74 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_77 : packedMul r74 r57 = r75 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_78 : packedMul r75 r55 = r76 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_79 : packedMul r76 r57 = r77 :=
  packed_of_list _ _ _ (by decide +kernel)
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.AmbientLineCertificates
