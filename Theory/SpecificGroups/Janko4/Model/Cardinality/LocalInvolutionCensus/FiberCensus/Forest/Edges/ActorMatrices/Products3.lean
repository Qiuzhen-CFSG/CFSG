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

theorem product_49 : packedMul partRows36 partRows20 = partRows49 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_50 : packedMul partRows48 partRows49 = partRows50 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_51 : packedMul partRows37 partRows38 = partRows51 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_52 : packedMul partRows13 partRows15 = partRows52 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_53 : packedMul partRows51 partRows52 = partRows53 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_54 : packedMul partRows50 partRows53 = wordRows1_2 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_55 : packedMul w14Rows partRows31 = partRows55 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_56 : packedMul partRows32 partRows9 = partRows56 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_57 : packedMul partRows55 partRows56 = partRows57 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_58 : packedMul partRows16 partRows13 = partRows58 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_59 : packedMul partRows36 partRows39 = partRows59 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_60 : packedMul partRows58 partRows59 = partRows60 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_61 : packedMul partRows57 partRows60 = partRows61 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_62 : packedMul partRows8 partRows12 = partRows62 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_63 : packedMul partRows4 partRows3 = partRows63 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_64 : packedMul partRows62 partRows63 = partRows64 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.ActorMatrices
