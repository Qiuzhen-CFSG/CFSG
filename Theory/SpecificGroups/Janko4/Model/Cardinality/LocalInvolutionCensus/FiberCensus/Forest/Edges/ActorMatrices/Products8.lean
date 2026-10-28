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

theorem product_129 : packedMul w10Rows partRows45 = partRows129 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_130 : packedMul partRows26 partRows41 = partRows130 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_131 : packedMul partRows17 partRows130 = partRows131 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_132 : packedMul partRows129 partRows131 = partRows132 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_133 : packedMul partRows128 partRows132 = wordRows3_4 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.ActorMatrices
