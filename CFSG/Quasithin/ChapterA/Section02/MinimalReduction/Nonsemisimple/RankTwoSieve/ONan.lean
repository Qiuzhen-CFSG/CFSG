module

public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankReduction
public import Theory.SpecificGroups.ONan.TwoRankLower

/-!
# The O’Nan branch of the source two-rank sieve

The actual eight-element subgroup excludes the O’Nan carrier.
The source application uses the literal central quotient and the already
proved rank reduction from the original counterexample and proper-section IH.
Source: Aschbacher–Smith A.2.12, printed p.36.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
/-- The O’Nan catalogue entry has two-rank greater than two. -/
theorem no_onan_model {Q : Type u} [Group Q] [Finite Q]
    (hr : primeRank 2 Q ≤ 2) (a : Q ≃* KnownSimple.SporadicName.onan.Carrier) : False := by
  let : Finite KnownSimple.SporadicName.onan.Carrier := Finite.of_equiv Q a.toEquiv
  have hb : 3 ≤ primeRank 2 KnownSimple.SporadicName.onan.Carrier :=
    ONan.TwoRankLower.three_le_twoRank
  rw [← Theory.GroupTheory.primeRank_equiv 2 a] at hb
  omega
end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}
/-- The actual source quotient cannot be the O’Nan carrier. -/
theorem CounterexampleToTheoremA.centralQuotient_no_onan_model
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) (a : (S ⧸ center S) ≃* KnownSimple.SporadicName.onan.Carrier) : False :=
  Nonsemisimple.RankTwoSieve.no_onan_model
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) a
end CFSG.Quasithin.ChapterA.Section02
