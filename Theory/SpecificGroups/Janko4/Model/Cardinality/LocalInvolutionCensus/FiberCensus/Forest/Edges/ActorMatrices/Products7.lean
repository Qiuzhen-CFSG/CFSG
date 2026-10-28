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

theorem product_113 : packedMul partRows21 inverseYRows = partRows113 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_114 : packedMul partRows5 partRows11 = partRows114 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_115 : packedMul partRows15 partRows114 = partRows115 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_116 : packedMul partRows113 partRows115 = partRows116 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_117 : packedMul partRows112 partRows116 = wordRows3_2 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_118 : packedMul partRows40 partRows10 = partRows118 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_119 : packedMul partRows31 partRows30 = partRows119 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_120 : packedMul partRows118 partRows119 = partRows120 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_121 : packedMul partRows16 partRows38 = partRows121 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_122 : packedMul partRows46 partRows4 = partRows122 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_123 : packedMul partRows26 partRows122 = partRows123 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_124 : packedMul partRows121 partRows123 = partRows124 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_125 : packedMul partRows120 partRows124 = wordRows3_3 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_126 : packedMul partRows29 partRows25 = partRows126 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_127 : packedMul partRows25 partRows12 = partRows127 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_128 : packedMul partRows126 partRows127 = partRows128 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.ActorMatrices
