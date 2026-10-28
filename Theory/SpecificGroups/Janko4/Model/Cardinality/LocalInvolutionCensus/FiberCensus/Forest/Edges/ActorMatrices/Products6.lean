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

theorem product_97 : packedMul partRows6 partRows96 = partRows97 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_98 : packedMul partRows95 partRows97 = partRows98 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_99 : packedMul partRows15 partRows25 = partRows99 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_100 : packedMul partRows25 w10Rows = partRows100 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_101 : packedMul partRows5 partRows100 = partRows101 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_102 : packedMul partRows99 partRows101 = partRows102 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_103 : packedMul partRows98 partRows102 = wordRows3_0 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_104 : packedMul partRows45 partRows46 = partRows104 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_105 : packedMul partRows42 partRows104 = partRows105 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_106 : packedMul partRows47 partRows8 = partRows106 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_107 : packedMul wordRows1_0 partRows44 = partRows107 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_108 : packedMul partRows106 partRows107 = partRows108 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_109 : packedMul partRows105 partRows108 = wordRows3_1 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_110 : packedMul partRows43 partRows5 = partRows110 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_111 : packedMul partRows33 partRows47 = partRows111 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_112 : packedMul partRows110 partRows111 = partRows112 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.ActorMatrices
