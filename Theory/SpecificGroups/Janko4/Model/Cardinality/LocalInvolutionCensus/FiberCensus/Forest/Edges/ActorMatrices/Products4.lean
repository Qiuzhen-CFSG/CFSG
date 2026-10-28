module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.ActorMatrices.Data

/-!
# Checked full-matrix subword products

Each product checks all 112 packed rows by kernel reduction.
`decode_packedMul` supplies the ordinary binary-matrix semantics.

Source: ATLAS of Finite Group Representations, R. A. Wilson,
S. J. Nickerson, J. N. Bray, unchanged `J4G1-max2W1` outputs.
See `ActorMatrices/source/README.md` for the inputs and proof boundaries.
-/

public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.ActorMatrices
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound Janko4.GeneratorCertificates KernelRows

set_option maxRecDepth 10000

theorem product_65 : packedMul partRows9 partRows37 = partRows65 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_66 : packedMul partRows30 wordRows1_0 = partRows66 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_67 : packedMul partRows39 partRows66 = partRows67 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_68 : packedMul partRows65 partRows67 = partRows68 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_69 : packedMul partRows64 partRows68 = partRows69 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_70 : packedMul partRows61 partRows69 = wordRows1_3 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_71 : packedMul partRows40 partRows9 = partRows71 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_72 : packedMul partRows31 partRows41 = partRows72 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_73 : packedMul wordRows1_0 partRows72 = partRows73 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_74 : packedMul partRows71 partRows73 = wordRows2_0 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_75 : packedMul w14Rows partRows13 = partRows75 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_76 : packedMul partRows7 partRows33 = partRows76 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_77 : packedMul partRows75 partRows76 = partRows77 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_78 : packedMul partRows33 w14Rows = partRows78 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_79 : packedMul partRows10 wordRows1_0 = partRows79 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_80 : packedMul partRows9 partRows79 = partRows80 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.ActorMatrices
