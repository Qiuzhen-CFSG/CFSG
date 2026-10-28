module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.TwoRank.Certificate
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.Structure
public import Theory.GroupTheory.PrimeRankSylow

/-!
# The intrinsic two-rank bound for the degree-100 HS carrier

The sixteen-color certificate bounds every elementary subgroup of the marked
Sylow two-subgroup. Sylow conjugacy and the elementary characterization of
prime rank give the same bound for the actual HS carrier.

Source: Aschbacher--Smith, G.7.3(2), printed p.348 (PDF p.359).
This is the intrinsic part of the automorphism-rank estimate used there.
-/

public section
namespace Sporadic.LeechRelated.HS
open Theory.GroupTheory

/-- The marked Sylow two-subgroup has two-rank at most four. -/
theorem sylow_twoRank_le_four : primeRank 2 EvenLocalCandidates.subgroup ≤ 4 := by
  apply (primeRank_le_iff_elementary_card_le EvenLocalCandidates.subgroup).mpr
  intro E hE
  let := hE
  exact TwoRankCertificate.elementary_card_le E

/-- The exact degree-100 ATLAS carrier has two-rank at most four. -/
theorem twoRank_le_four : primeRank 2 Carrier ≤ 4 := by
  rw [BlockNormalizer.baseSylow.primeRank_eq]
  exact sylow_twoRank_le_four

end Sporadic.LeechRelated.HS
