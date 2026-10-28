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

theorem product_81 : packedMul partRows78 partRows80 = partRows81 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_82 : packedMul partRows77 partRows81 = wordRows2_1 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_83 : packedMul partRows4 partRows10 = partRows83 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_84 : packedMul partRows42 partRows83 = partRows84 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_85 : packedMul partRows30 partRows3 = partRows85 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_86 : packedMul partRows34 wordRows1_0 = partRows86 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_87 : packedMul partRows85 partRows86 = partRows87 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_88 : packedMul partRows84 partRows87 = wordRows2_2 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_89 : packedMul partRows11 partRows25 = partRows89 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_90 : packedMul partRows43 partRows89 = partRows90 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_91 : packedMul partRows13 partRows17 = partRows91 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_92 : packedMul partRows44 inverseYRows = partRows92 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_93 : packedMul partRows91 partRows92 = partRows93 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_94 : packedMul partRows90 partRows93 = wordRows2_3 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_95 : packedMul partRows35 partRows24 = partRows95 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_96 : packedMul partRows5 partRows19 = partRows96 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.ActorMatrices
