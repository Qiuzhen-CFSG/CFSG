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
theorem product_40 : packedMul r36 r36 = r32 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_41 : packedMul r32 r33 = r37 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_42 : packedMul r35 r37 = r38 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_43 : packedMul r38 r38 = r34 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_44 : packedMul Janko4.bRows Janko4.bRows = r39 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_45 : packedMul r39 Janko4.aRows = r40 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_46 : packedMul Janko4.bRows r41 = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_47 : packedMul r40 r41 = r42 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_48 : packedMul r42 Janko4.aRows = r43 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_49 : packedMul r43 Janko4.bRows = r44 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_50 : packedMul r44 r45 = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_51 : packedMul r45 r34 = r46 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_52 : packedMul r46 r44 = r47 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_53 : packedMul r47 r49 = r48 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_54 : packedMul r48 r48 = r50 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_55 : packedMul r48 r50 = r51 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_56 : packedMul r51 r51 = r52 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_57 : packedMul r44 r52 = r53 :=
  packed_of_list _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_58 : packedMul r55 r54 = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_59 : packedMul r54 r57 = r56 :=
  packed_of_list _ _ _ (by decide +kernel)
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.AmbientLineCertificates
