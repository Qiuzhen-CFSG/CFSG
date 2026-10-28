module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.RankOneEightCharacteristic
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# The marked elementary eight in Rudvalis

The existing three-word certificate proves that the marked subgroup has
exponent two and order eight in the original ATLAS carrier. Its inclusion
supplies the rank obstruction in Aschbacher–Smith A.2.12, printed p.36.
-/

namespace Rudvalis
open SylowOvergroups.RadicalCoverage.LocalCover
open SylowOvergroups.RadicalCoverage.LocalCover.RankOneEightCharacteristic
/-- The actual marked eight witnesses the Rudvalis rank obstruction. -/
public theorem three_le_twoRank : 3 ≤ primeRank 2 Model := by
  let : IsElementaryAbelian 2 (elementary 2) := elementary_two_elementary
  exact IsElementaryAbelian.primeRank_ge_of_card (elementary 2) elementary_two_card
end Rudvalis
