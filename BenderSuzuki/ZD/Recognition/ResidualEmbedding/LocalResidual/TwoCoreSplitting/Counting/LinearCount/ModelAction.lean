module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Counting.LinearCount.ModelAction.Evaluations
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Counting.LinearCount.ModelAction.NoBorel

/-!
# Concrete model actions for the Section 17 count

The four branch theorems identify the original circle stabilizer as the
prescribed Sylow normalizer, compute the Sylow order and degree, and evaluate
the literal relative centralizer index as q−1. The unitary no-Borel theorems
apply the source fixed-set clause to the actual SU₃ or PSU₃ image of D₀.

Both unitary carriers permit arbitrary Hermitian forms. All model equivalences,
field cardinalities, marked involutions and the original subgroup embeddings
are retained. Final counting and model elimination belong to LinearCount.

Source: GLS4, Chapter 2, (17D), Lemmas 17.2(a,e), 17.4; Chapter 4, Lemmas 3.2, 3.11.
-/
