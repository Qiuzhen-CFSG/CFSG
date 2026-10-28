module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismTwoRank
public import Theory.GroupTheory.PrimeRankCentralCover

/-!
# The HS automorphism-rank input to G.7

The actual degree-100 ATLAS carrier has automorphism two-rank at most five:
its intrinsic rank is at most four and its outer group has order dividing two.
Faithful automorphism descent for a perfect group transfers this bound through
the literal quotient by its whole center. Thus the source component need not
be identified with its central quotient.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the discarded
HS case of G.7.3(2), printed p.348 (PDF p.359). The independent degree-twenty
input from G.7.2(6) is provided by `SporadicLocal.OddSubgroups`.
-/

public section
namespace CFSG.Quasithin.ChapterG.Section07.SporadicLocal
open Subgroup Theory.GroupTheory Sporadic.LeechRelated

/-- The HS automorphism bound on the exact source carrier, with every model premise discharged. -/
theorem hs_automorphism_twoRank_le_five : primeRank 2 (MulAut HS.Carrier) ≤ 5 :=
  HS.automorphism_twoRank_le_five

/-- The same bound for the actual perfect central cover of HS in the source argument. -/
theorem hs_centralQuotient_automorphism_twoRank_le_five
    {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    (e : L ⧸ center L ≃* HS.Carrier) : primeRank 2 (MulAut L) ≤ 5 := by
  have h := automorphism_primeRank_le_quotient_center (E := L) 2
  rw [primeRank_equiv 2 (MulAut.congr e)] at h
  exact h.trans hs_automorphism_twoRank_le_five

end CFSG.Quasithin.ChapterG.Section07.SporadicLocal
