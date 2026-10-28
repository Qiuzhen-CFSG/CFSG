module

public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankReduction
public import Theory.Mathieu.TwoRankLower
public import Theory.SpecificGroups.Janko1.TwoRank

/-!
# Five sporadic exclusions in the source two-rank-two branch

Transport the actual elementary-subgroup rank bounds for M₁₂, M₂₂, M₂₃,
M₂₄ and J₁ through the isomorphisms in the complete sporadic catalogue.
The source application uses the original counterexample's proved rank bound
on S/Z(S), with no quotient-quasithinness assumption.
Source: Aschbacher–Smith A.2.12, printed p.36.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u

/-- The named elementary subgroups rule out these five actual catalogue entries. -/
theorem no_mathieu_janko_one_model {Q : Type u} [Group Q] [Finite Q]
    (hr : primeRank 2 Q ≤ 2) (name : KnownSimple.SporadicName)
    (hname : name = .m12 ∨ name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .j1)
    (a : Q ≃* name.Carrier) : False := by
  have hb : 3 ≤ primeRank 2 name.Carrier := by
    rcases hname with rfl | rfl | rfl | rfl | rfl
    · exact Sporadic.Mathieu.m12_three_le_twoRank
    · exact (by decide : 3 ≤ 4).trans Sporadic.Mathieu.m22_four_le_twoRank
    · exact (by decide : 3 ≤ 4).trans Sporadic.Mathieu.m23_four_le_twoRank
    · exact (by decide : 3 ≤ 6).trans Sporadic.Mathieu.m24_six_le_twoRank
    · exact Janko1.three_le_twoRank
  let : Finite name.Carrier := Finite.of_equiv Q a.toEquiv
  rw [← Theory.GroupTheory.primeRank_equiv 2 a] at hb
  omega

end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

/-- Literal application of the five sporadic exclusions to the source quotient. -/
theorem CounterexampleToTheoremA.centralQuotient_no_mathieu_janko_one_model
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) (name : KnownSimple.SporadicName)
    (hname : name = .m12 ∨ name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .j1)
    (a : (S ⧸ center S) ≃* name.Carrier) : False :=
  Nonsemisimple.RankTwoSieve.no_mathieu_janko_one_model
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) name hname a

end CFSG.Quasithin.ChapterA.Section02
