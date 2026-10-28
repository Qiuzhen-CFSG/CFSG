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

theorem product_17 : packedMul partRows4 partRows12 = partRows17 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_18 : packedMul partRows14 partRows9 = partRows18 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_19 : packedMul partRows12 partRows13 = partRows19 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_20 : packedMul partRows17 partRows8 = partRows20 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_21 : packedMul partRows10 partRows10 = partRows21 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_22 : packedMul partRows13 partRows19 = partRows22 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_23 : packedMul partRows22 partRows20 = partRows23 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_24 : packedMul partRows23 partRows9 = partRows24 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_25 : packedMul partRows12 partRows5 = partRows25 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_26 : packedMul partRows4 partRows4 = partRows26 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_27 : packedMul partRows14 partRows18 = partRows27 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_28 : packedMul partRows27 partRows21 = partRows28 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_29 : packedMul partRows24 partRows3 = partRows29 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_30 : packedMul partRows16 partRows16 = partRows30 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_31 : packedMul partRows3 partRows10 = partRows31 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_32 : packedMul partRows8 partRows3 = partRows32 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.ActorMatrices
