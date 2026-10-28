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
theorem product_200 : packedMul r99 r196 = r197 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_201 : packedMul r22 r197 = r198 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_202 : packedMul r120 r198 = r199 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_203 : packedMul r142 r199 = r200 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_204 : packedMul r120 r200 = r201 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_205 : packedMul r186 r201 = r202 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_206 : packedMul r172 r202 = r203 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_207 : packedMul r203 r193 = r204 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_208 : packedMul r204 r22 = r205 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_209 : packedMul r205 r98 = r206 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_210 : packedMul r206 r98 = r207 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_211 : packedMul r207 r25 = r208 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_212 : packedMul r208 r99 = r209 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_213 : packedMul r209 r99 = r210 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_214 : packedMul r210 r26 = r211 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_215 : packedMul r211 r25 = r212 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_216 : packedMul r212 r156 = r213 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_217 : packedMul r213 r143 = r214 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_218 : packedMul r214 r121 = r215 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_219 : packedMul r215 r216 = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.AmbientLineCertificates
