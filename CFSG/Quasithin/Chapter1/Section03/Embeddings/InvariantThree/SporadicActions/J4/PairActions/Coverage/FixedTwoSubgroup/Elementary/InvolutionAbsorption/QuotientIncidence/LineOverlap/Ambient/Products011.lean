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
theorem product_220 : packedMul r104 r98 = r217 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_221 : packedMul r217 r98 = r218 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_222 : packedMul r218 r22 = r219 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_223 : packedMul r219 r25 = r220 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_224 : packedMul r220 r142 = r221 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_225 : packedMul r221 r155 = r222 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_226 : packedMul r222 r121 = r223 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_227 : packedMul r223 r216 = r224 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_228 : packedMul r224 r225 = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_229 : packedMul r105 r22 = r226 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_230 : packedMul r226 r104 = r227 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_231 : packedMul r227 r98 = r228 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_232 : packedMul r228 r104 = r229 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_233 : packedMul r229 r98 = r230 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_234 : packedMul r230 r26 = r231 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_235 : packedMul r231 r142 = r232 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_236 : packedMul r232 r155 = r233 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_237 : packedMul r233 r121 = r234 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_238 : packedMul r234 r235 = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_239 : packedMul r99 r105 = r236 :=
  packed_of_list _ _ _ (by decide +kernel)
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.AmbientLineCertificates
