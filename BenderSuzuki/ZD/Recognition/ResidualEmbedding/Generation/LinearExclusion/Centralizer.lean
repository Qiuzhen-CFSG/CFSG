module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.InitialStructure
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.NormalizerGeometry
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.SourceInterfaces
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.PairResidual

/-!
# The proper PSL₂ centralizer argument

The original context supplies the initial centralizer structure, even-subgroup
normalizer control, and the local index q². Involution transport gives the TI
property for the actual O₂(C_G(L)); nontriviality is still an earlier-source
obligation. The pair residual consequence is already proved conditional on
the source order |C_G(L)|=2.

The full conjunction from GLS IV, Chapter 2, Lemma 15.6 and the paragraph
after Lemma 15.7 remains to be assembled here. `SourceInterfaces` records
its independent Lemmas 15.2–15.5 obligations without asserting them.
The remaining conditional counting proof must also identify the actual
normal closure inside M. No conclusion of Lemma 15.7 is needed for this
centralizer argument.
-/
