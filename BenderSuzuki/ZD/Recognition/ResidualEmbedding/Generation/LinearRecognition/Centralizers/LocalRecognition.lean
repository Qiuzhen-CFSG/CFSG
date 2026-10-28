module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.LocalRecognition.FixedSize
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.LocalRecognition.Conjugacy
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.LocalRecognition.Source

/-!
# Local recognition for proper residual centralizers

`FixedSize` proves `qᵥ > 2` and its exact binary exponent from the original
proper-residual hypotheses, including the fusion/transfer exclusion of two.
`Conjugacy` proves Lemma 12.4(d) on the punctured distinguished coset.

`Source` assembles all five fields of `ResidualCentralizerLocalData` from
the original proper-residual hypotheses. The unitary-cover alternatives,
involutory action, actual odd-core quotient and centralizer factorization
are supplied by their completed source proofs, retaining both PSU₃ and SU₃.
The later shearing, counting and unitary-exclusion arguments remain separate.

Source: GLS4, Chapter 2, Lemmas 12.3–12.4,
`refs/KGroup/GLS4/Chapter2.tex`.
-/
