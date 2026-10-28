module
public import Theory.SpecificGroups.LieType.TwoRankLower.BinaryExceptional
public import Theory.SpecificGroups.LieType.TwoRankLower.OddTwistedE6
public import CFSG.KnownSimple.ExceptionalModels
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankReduction
/-!
# Every twisted E6 carrier in the original two-rank sieve

The binary Sp6 section and the odd graph-fixed sign actors give the same
ordinary two-rank obstruction, without a quotient-quasithinness assumption.
Source: Aschbacher--Smith A.2.12, printed p.36.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
variable {Q : Type u} [Group Q] [Finite Q]
/-- The full twisted E6 model is absent from the ordinary two-rank-two list. -/
theorem no_twisted_e6_model (hr : primeRank 2 Q ≤ 2) {q : ℕ}
    (model : ExceptionalGroup.IsTwistedE6 Q q) : False := by
  obtain ⟨p,m,hp,_,⟨e⟩⟩ := model
  have hb : 3 ≤ primeRank 2 (TwistedE6.Model p m) := by
    by_cases h2 : p = 2
    · subst p
      exact Theory.SpecificGroups.LieType.TwoRank.twisted_e6_three_le m
    · exact TwistedE6.RankFour.TwoRank.three_le p m h2
  rw [← primeRank_equiv 2 e] at hb
  omega
end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p q : ℕ}
/-- The original source central quotient cannot be twisted E6 at any parameter. -/
theorem CounterexampleToTheoremA.centralQuotient_no_twisted_e6_model
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G)
    (model : ExceptionalGroup.IsTwistedE6 (S ⧸ center S) q) : False :=
  Nonsemisimple.RankTwoSieve.no_twisted_e6_model
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) model
end CFSG.Quasithin.ChapterA.Section02
