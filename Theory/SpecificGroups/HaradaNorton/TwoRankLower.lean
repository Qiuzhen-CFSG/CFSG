module

public import Theory.SpecificGroups.HaradaNorton.ProperAlternatingTwelve
public import Theory.SpecificGroups.Alternating.TwoRankSieve
public import Theory.GroupTheory.QuasithinBasic

/-!
# Harada–Norton's alternating subgroup witnesses two-rank at least three

The actual ATLAS A₁₂ word embedding contains the regular elementary eight
on eight letters. Source: GLS3 Table 5.3w; Aschbacher–Smith A.2.12, p.36.
-/

namespace HaradaNorton
/-- The genuine alternating subgroup gives the required two-rank obstruction. -/
public theorem three_le_twoRank : 3 ≤ primeRank 2 HN :=
  (alternatingGroup.TwoRankSieve.three_le_primeRank (by decide : 8 ≤ 12)).trans
    (Theory.GroupTheory.primeRank_le_of_injective 2
      OrderCertificate.alternatingTwelveEmbedding
      OrderCertificate.alternatingTwelveEmbedding_injective)
end HaradaNorton
