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

theorem product_33 : packedMul partRows5 partRows15 = partRows33 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_34 : packedMul partRows18 partRows8 = partRows34 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_35 : packedMul partRows28 partRows8 = partRows35 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_36 : packedMul partRows15 partRows11 = partRows36 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_37 : packedMul partRows6 partRows16 = partRows37 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_38 : packedMul w14Rows partRows5 = partRows38 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_39 : packedMul partRows3 partRows14 = partRows39 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_40 : packedMul inverseYRows partRows8 = partRows40 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_41 : packedMul partRows3 wordRows1_0 = partRows41 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_42 : packedMul partRows28 inverseYRows = partRows42 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_43 : packedMul partRows29 partRows5 = partRows43 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_44 : packedMul partRows34 partRows32 = partRows44 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_45 : packedMul partRows15 partRows4 = partRows45 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_46 : packedMul partRows11 partRows26 = partRows46 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_47 : packedMul partRows9 partRows8 = partRows47 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_48 : packedMul partRows35 partRows29 = partRows48 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.ActorMatrices
