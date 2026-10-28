module

public import Theory.SpecificGroups.Janko1.Model.SylowTwo
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# The elementary Sylow subgroup gives J₁ two-rank at least three

The certified Sylow two-subgroup of the actual seven-dimensional matrix
carrier is elementary of order eight. Its inclusion proves the lower bound
needed to exclude J₁ in Aschbacher–Smith A.2.12, printed p.36.
-/

namespace Janko1
/-- Every actual Sylow two-subgroup witnesses the required rank obstruction. -/
public theorem three_le_twoRank : 3 ≤ primeRank 2 Model := by
  let S : Sylow 2 Model := default
  let : IsElementaryAbelian 2 S := SylowTwo.elementary S
  exact IsElementaryAbelian.primeRank_ge_of_card S.toSubgroup (SylowTwo.card S)
end Janko1
