module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.SimpleQuotient
public import Theory.SpecificGroups.HaradaNorton.TwoRankLower
public import Theory.SpecificGroups.BabyMonster.TwoRankLower
public import Theory.SpecificGroups.Monster.TwoRankLower

/-!
# Three large sporadic carriers excluded by their actual local embeddings

The A₁₂ subgroup of HN, A₉ subgroup of the Baby Monster, and cocode subgroup
of the Griess group all contain elementary eights. Finite and nontrivial
carrier instances are transported from the actual source quotient, whose
simplicity follows from the original nonsemisimple reduction.
Source: Aschbacher–Smith A.2.12, printed p.36.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
/-- Three actual local embeddings exclude HN, the Baby Monster, and the Monster. -/
theorem no_three_large_sporadic_models {Q : Type u} [Group Q] [Finite Q] [Nontrivial Q]
    (hr : primeRank 2 Q ≤ 2) (name : KnownSimple.SporadicName)
    (hname : name = .hn ∨ name = .babyMonster ∨ name = .monster)
    (a : Q ≃* name.Carrier) : False := by
  let : Finite name.Carrier := Finite.of_equiv Q a.toEquiv
  let : Nontrivial name.Carrier := a.toEquiv.symm.nontrivial
  have hb : 3 ≤ primeRank 2 name.Carrier := by
    rcases hname with rfl | rfl | rfl
    · exact HaradaNorton.three_le_twoRank
    · let : Finite BabyMonster.Carrier := Finite.of_equiv Q a.toEquiv
      let : Nontrivial BabyMonster.Carrier := a.toEquiv.symm.nontrivial
      exact BabyMonster.three_le_twoRank
    · let : Finite Sporadic.Monster.GriessGroup := Finite.of_equiv Q a.toEquiv
      exact (by decide : 3 ≤ 12).trans Sporadic.Monster.TwoRank.twelve_le_twoRank
  rw [← Theory.GroupTheory.primeRank_equiv 2 a] at hb
  omega
end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}
/-- The actual source central quotient is none of these three large sporadic carriers. -/
theorem CounterexampleToTheoremA.centralQuotient_no_three_large_sporadic_models
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) (name : KnownSimple.SporadicName)
    (hname : name = .hn ∨ name = .babyMonster ∨ name = .monster)
    (a : (S ⧸ center S) ≃* name.Carrier) : False := by
  let := h.section_centralQuotient_simple_of_not_semisimple ih hn
  exact Nonsemisimple.RankTwoSieve.no_three_large_sporadic_models
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) name hname a
end CFSG.Quasithin.ChapterA.Section02
