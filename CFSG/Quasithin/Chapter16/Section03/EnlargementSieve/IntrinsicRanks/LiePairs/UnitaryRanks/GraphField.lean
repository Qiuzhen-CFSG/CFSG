module

public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.IntrinsicRanks.LiePairs
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.IntrinsicRanks.LiePairs.UnitaryRanks

/-!
# Exclusion of the linear/unitary graph-field pair

The actual source models `K ≅ PSL₃(2^(2*n))` and `L ≅ PSU₃(2^n)` have
two-rank `4*n` and automorphism two-rank at most `n+1`, respectively.
For `n > 1` they contradict the ambient rank bound in the ordinary-pair
sieve. The unitary automorphism estimate is now an intrinsic theorem, so
this application has no additional numerical or coverage premise.

Source: Aschbacher–Smith 16.1.7(3b), printed p.1172, and its elimination in
16.3.9, p.1180, using the corrected automorphism bound from p.356.
-/

public section

namespace CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.LiePairs

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
  {z t : G} {L : Subgroup G}

/-- Discharge the unitary automorphism-rank input of the actual ordinary-pair
elimination, retaining both source model witnesses on their original carriers. -/
theorem exclude_linearThree_graphField_of_unitary
    (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t) {n : ℕ} (hn : 1 < n)
    (hK : ClassicalGroup.IsPSL (enlargement t L) 3 (2 ^ (2 * n)))
    (hL : ClassicalGroup.IsPSU L 3 (2 ^ n)) : False :=
  exclude_linearThree_graphField h hs hn hK
    (unitaryThree_automorphism_rank_le (by omega) hL)

end CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.LiePairs
