module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Reduction
public import Theory.SpecificGroups.Alternating.EightNineInvolutionCounts

/-!
# Certified finite model counts for the nonnormal index calculation

The reusable permutation calculation checks the actual mixed conjugacy-class
fibers in A₈ and A₉, with the half-order power convention used by Thompson's
formula. These three numerical results discharge `Index.ModelCounts`.
The application below retains the source marking and second-centralizer
comparison as explicit inputs; it requires no further model-count premise.

Source: Aschbacher, “A 2-local characterization of M12”, Proposition 3.3,
printed p.38, the comparison of centralizers and fusion with A₉.
-/

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index

/-- The checked finite calculations, with the literal source permutations. -/
public theorem modelCounts : ModelCounts where
  eight_z := alternatingGroup.EightNineInvolutionCounts.Eight.kappa_eq
  nine_t := alternatingGroup.EightNineInvolutionCounts.Nine.kappa_eq
  nine_centralizer := alternatingGroup.EightNineInvolutionCounts.card_centralizer_t9

/-- The finite-model premise of the index reduction is now discharged. -/
public theorem index_nine_of_certified_centralizer_comparison
    {G : Type*} [Group G] [Finite G] {z : G} (h : Hypotheses z)
    {L : Subgroup G} (d : InvolutionData z L) (hL : Odd L.index)
    (hCL : Centralizer z ≤ L) (c : SecondCentralizerData d) : L.index = 9 :=
  index_nine_of_centralizer_comparison h d hL hCL c modelCounts

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index
