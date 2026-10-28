module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCore
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Reduction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearNormalizer

/-!
# Self-normalization of the J₄ local two-core action

Let C be the literal involution centralizer and Q = O₂(C). Under the explicit
centralizer-control hypothesis, `Comparison` constructs the action of Aut(Q)
on Q/Z(Q) in binary coordinates. Its kernel is contained in Inn(Q), and it
maps the conjugation image of C onto the specified matrix group.

`LinearNormalizer` proves that this matrix group is self-normalizing.
Since the conjugation image contains Inn(Q), it is the full preimage of
the matrix group. The transfer in `Reduction` therefore proves that the
conjugation image is self-normalizing in Aut(Q). All comparison and matrix
normalizer premises are discharged; centralizer control remains the parent
local-action theorem's input.

Source motivation: GLS3, Table 5.3i, printed p.270,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`, gives the centralizer shape
`2^(1+12).(3M22.2)`. The self-normalizer calculation is proved separately;
it is not an assertion of that table.
-/

public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares

/-- Every automorphism of the actual two-core that normalizes the conjugation
image of the literal involution centralizer is induced by that centralizer. -/
theorem localTwoCoreActionSelfNormalizer
    (hcent : LocalTwoCoreCentralizerControl) : LocalTwoCoreActionSelfNormalizer :=
  localTwoCoreActionSelfNormalizer_of_linearComparison
    (localTwoCoreLinearComparison hcent) TwoCoreLinearModel.actionGroup_selfNormalizer

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares
