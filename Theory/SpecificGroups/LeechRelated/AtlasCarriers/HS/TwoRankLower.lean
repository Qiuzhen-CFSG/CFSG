module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.RankOneFourNormalizer.Fixed
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# The marked elementary eight in Higman–Sims

The third certified elementary row has order eight. Its literal inclusion
supplies the lower two-rank bound used in Aschbacher–Smith A.2.12, printed p.36.
The words and action convention are those of the imported ATLAS model.
-/

namespace Sporadic.LeechRelated.HS
/-- The actual marked eight witnesses the Higman–Sims rank obstruction. -/
public theorem three_le_twoRank : 3 ≤ primeRank 2 Carrier := by
  let : IsElementaryAbelian 2 (EvenLocalCandidates.elementary 2) :=
    EvenLocalCandidates.elementary_isElementaryAbelian 2
  exact IsElementaryAbelian.primeRank_ge_of_card (EvenLocalCandidates.elementary 2)
    (RankOneFourNormalizer.elementary_card 2)
end Sporadic.LeechRelated.HS
