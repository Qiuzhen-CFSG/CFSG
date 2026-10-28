module

public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankReduction
public import Theory.SpecificGroups.Janko3.TwoRankLower

/-!
# The J₃ branch of the source two-rank sieve

The actual sixteen-element translation subgroup excludes the J₃ carrier.
The source application uses the literal central quotient and the already
proved rank reduction from the original counterexample and proper-section IH.
Source: Aschbacher–Smith A.2.12, printed p.36.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
/-- The J₃ catalogue entry has two-rank greater than two. -/
theorem no_janko_three_model {Q : Type u} [Group Q] [Finite Q]
    (hr : primeRank 2 Q ≤ 2) (a : Q ≃* KnownSimple.SporadicName.j3.Carrier) : False := by
  let : Finite KnownSimple.SporadicName.j3.Carrier := Finite.of_equiv Q a.toEquiv
  have hb : 4 ≤ primeRank 2 KnownSimple.SporadicName.j3.Carrier :=
    Sporadic.Janko3.TwoRank.four_le_twoRank
  rw [← Theory.GroupTheory.primeRank_equiv 2 a] at hb
  omega
end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}
/-- The actual source quotient cannot be the J₃ carrier. -/
theorem CounterexampleToTheoremA.centralQuotient_no_janko_three_model
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) (a : (S ⧸ center S) ≃* KnownSimple.SporadicName.j3.Carrier) : False :=
  Nonsemisimple.RankTwoSieve.no_janko_three_model
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) a
end CFSG.Quasithin.ChapterA.Section02
