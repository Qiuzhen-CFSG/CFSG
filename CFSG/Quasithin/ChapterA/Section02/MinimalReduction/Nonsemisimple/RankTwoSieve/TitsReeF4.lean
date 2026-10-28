module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankReduction
public import Theory.SpecificGroups.ReeF4.TwoRankLower

/-!
# The Tits and Ree F₄ exclusions in the source two-rank sieve

Actual elementary eights exclude both the full Ree F₄ family and the separate
Tits simple carrier. The last applications use the proved two-rank bound on
the original counterexample's quotient S/Z(S).
Source: Aschbacher–Smith A.2.12, printed p.36.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
variable {Q : Type u} [Group Q] [Finite Q]

/-- The literal Tits simple carrier is absent from the two-rank-two list. -/
theorem no_tits_model (hr : primeRank 2 Q ≤ 2) (a : Q ≃* Tits.ParrottGroup) : False := by
  have hb := Tits.TwoRank.three_le
  rw [← primeRank_equiv 2 a] at hb
  omega

/-- Every actual Ree F₄ catalogue entry is absent from the two-rank-two list. -/
theorem no_reeF4_model (hr : primeRank 2 Q ≤ 2) (hmodel : ReeF4.IsReeF4Model Q) : False := by
  obtain ⟨m, _, ⟨a⟩⟩ := hmodel
  have hb := ReeF4.three_le_twoRank m
  rw [← primeRank_equiv 2 a] at hb
  omega

end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

/-- The Tits endpoint is impossible for the literal source quotient. -/
theorem CounterexampleToTheoremA.centralQuotient_no_tits_model
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) (a : (S ⧸ center S) ≃* Tits.ParrottGroup) : False :=
  Nonsemisimple.RankTwoSieve.no_tits_model
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) a

/-- The entire Ree F₄ family is impossible for the literal source quotient. -/
theorem CounterexampleToTheoremA.centralQuotient_no_reeF4_model
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) (hmodel : ReeF4.IsReeF4Model (S ⧸ center S)) : False :=
  Nonsemisimple.RankTwoSieve.no_reeF4_model
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) hmodel

end CFSG.Quasithin.ChapterA.Section02
