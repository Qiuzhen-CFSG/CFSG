module

public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankReduction
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23.TwoRankLower

/-!
# The Fi₂₃ branch of the source two-rank sieve

The actual eight-element subgroup excludes the Fi₂₃ carrier.
The source application uses the literal central quotient and the already
proved rank reduction from the original counterexample and proper-section IH.
Source: Aschbacher–Smith A.2.12, printed p.36.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
/-- The Fi₂₃ catalogue entry has two-rank greater than two. -/
theorem no_fischer_twenty_three_model {Q : Type u} [Group Q] [Finite Q]
    (hr : primeRank 2 Q ≤ 2) (a : Q ≃* KnownSimple.SporadicName.fi23.Carrier) : False := by
  let : Finite KnownSimple.SporadicName.fi23.Carrier := Finite.of_equiv Q a.toEquiv
  have hb : 3 ≤ primeRank 2 KnownSimple.SporadicName.fi23.Carrier :=
    Sporadic.Fischer.Fi23.TwoRank.three_le_twoRank
  rw [← Theory.GroupTheory.primeRank_equiv 2 a] at hb
  omega
end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}
/-- The actual source quotient cannot be the Fi₂₃ carrier. -/
theorem CounterexampleToTheoremA.centralQuotient_no_fischer_twenty_three_model
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) (a : (S ⧸ center S) ≃* KnownSimple.SporadicName.fi23.Carrier) : False :=
  Nonsemisimple.RankTwoSieve.no_fischer_twenty_three_model
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) a
end CFSG.Quasithin.ChapterA.Section02
