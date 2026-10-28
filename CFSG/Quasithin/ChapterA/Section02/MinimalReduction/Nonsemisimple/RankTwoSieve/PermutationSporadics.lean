module

public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankReduction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.TwoRankLower
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.McL.TwoRankLower
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co3.TwoRankLower

/-!
# Three permutation carriers excluded by the source two-rank bound

Certified elementary eight-subgroups of J₂, McL and Co₃ exclude these exact
catalogue entries. The source application transports along the given model
of the literal central quotient S/Z(S).
Source: Aschbacher–Smith A.2.12, printed p.36.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
/-- The three permutation carriers have two-rank greater than two. -/
theorem no_three_permutation_models {Q : Type u} [Group Q] [Finite Q]
    (hr : primeRank 2 Q ≤ 2) (name : KnownSimple.SporadicName)
    (hname : name = .j2 ∨ name = .mcl ∨ name = .co3) (a : Q ≃* name.Carrier) : False := by
  let : Finite name.Carrier := Finite.of_equiv Q a.toEquiv
  have hb : 3 ≤ primeRank 2 name.Carrier := by
    rcases hname with rfl | rfl | rfl
    · exact Sporadic.LeechRelated.J2.TwoRank.three_le_twoRank
    · exact Sporadic.LeechRelated.McL.TwoRank.three_le_twoRank
    · exact Sporadic.LeechRelated.Co3.TwoRank.three_le_twoRank
  rw [← Theory.GroupTheory.primeRank_equiv 2 a] at hb
  omega
end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}
/-- J₂, McL and Co₃ cannot occur as the actual source central quotient. -/
theorem CounterexampleToTheoremA.centralQuotient_no_three_permutation_models
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) (name : KnownSimple.SporadicName)
    (hname : name = .j2 ∨ name = .mcl ∨ name = .co3)
    (a : (S ⧸ center S) ≃* name.Carrier) : False :=
  Nonsemisimple.RankTwoSieve.no_three_permutation_models
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) name hname a
end CFSG.Quasithin.ChapterA.Section02
