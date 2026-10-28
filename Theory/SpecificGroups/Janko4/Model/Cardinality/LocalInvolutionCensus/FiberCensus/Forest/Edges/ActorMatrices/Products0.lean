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

theorem product_xinv : packedMul w10Rows wordRows1_0 = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

theorem product_yinv : packedMul w14Rows inverseYRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

theorem product_3 : packedMul wordRows1_0 inverseYRows = partRows3 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_4 : packedMul w10Rows inverseYRows = partRows4 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_5 : packedMul w10Rows w14Rows = partRows5 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_6 : packedMul wordRows1_0 w14Rows = partRows6 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_7 : packedMul partRows4 partRows5 = partRows7 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_8 : packedMul partRows3 partRows3 = partRows8 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_9 : packedMul partRows6 partRows6 = partRows9 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_10 : packedMul partRows6 partRows8 = partRows10 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_11 : packedMul partRows4 partRows7 = partRows11 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_12 : packedMul partRows11 partRows5 = partRows12 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_13 : packedMul partRows7 partRows7 = partRows13 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_14 : packedMul partRows10 partRows9 = partRows14 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_15 : packedMul partRows5 partRows7 = partRows15 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_16 : packedMul partRows3 partRows6 = partRows16 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.ActorMatrices
