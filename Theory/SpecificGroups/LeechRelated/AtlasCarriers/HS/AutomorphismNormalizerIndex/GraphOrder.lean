module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.GraphOrder.Certificate

/-!
# An upper bound for the explicit HS graph automorphism group

The checked color refinements bound the successive orbits at vertices
`0, 4, 2, 14, 1, 3` by `100, 22, 21, 20, 16, 6`. The final coloring
is discrete. Multiplying the six orbit–stabilizer inequalities gives the
bound `88,704,000` for all permutations preserving the explicit adjacency.

This is the graph calculation used in the permutation-normalizer argument
associated with GLS3, Table 5.3m, printed p.274. It does not require the
order of the HS carrier or preservation of the graph by its normalizer.
-/

public section

namespace Sporadic.LeechRelated.HS.NormalizerIndex
open GraphOrder

/-- The full automorphism group of the explicit HS graph has order at most
`88,704,000`. -/
theorem graphGroup_card_le : Nat.card graphGroup ≤ 88704000 := by
  have h0 := Certificate.step0
  have h1 := Certificate.step1
  have h2 := Certificate.step2
  have h3 := Certificate.step3
  have h4 := Certificate.step4
  have h5 := Certificate.step5
  have h6 := Certificate.terminal_card
  rw [fixing_nil] at h0
  omega

end Sporadic.LeechRelated.HS.NormalizerIndex
