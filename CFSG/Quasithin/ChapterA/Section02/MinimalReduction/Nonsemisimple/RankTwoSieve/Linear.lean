module

public import CFSG.KnownSimple.ClassicalModels
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankReduction
public import Theory.SpecificGroups.Classical.LinearTwoRankLower

/-!
# The full split-linear branch of the source two-rank sieve

The actual elementary eight in every projective special linear group of
degree at least four forces a rank-two linear catalogue entry to have degree
two or three. The final application is to the literal source quotient S/Z(S).
Source: Aschbacher–Smith A.2.12, printed p.36.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
variable {Q : Type u} [Group Q] [Finite Q] {n q : ℕ}

/-- The actual linear model in the rank-two branch has degree at most three. -/
theorem linear_dimension_le_three (hr : primeRank 2 Q ≤ 2)
    (hmodel : ClassicalGroup.IsPSL Q n q) : n ≤ 3 := by
  by_contra hn
  obtain ⟨F,hF,hfin,_,⟨a⟩⟩ := hmodel
  have hb := Matrix.SpecialLinearGroup.LinearTwoRank.three_le_projectiveRank F (by omega : 4 ≤ n)
  rw [← Theory.GroupTheory.primeRank_equiv 2 a] at hb
  omega

/-- The admissible split-linear catalogue degrees reduce to two and three. -/
theorem linear_degree_two_or_three (hr : primeRank 2 Q ≤ 2) (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL Q n q) : n = 2 ∨ n = 3 := by
  have hd := linear_dimension_le_three hr hmodel
  omega

end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

/-- Literal application of the complete linear dimension bound to the source quotient. -/
theorem CounterexampleToTheoremA.centralQuotient_linear_dimension_le_three
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) {n q : ℕ}
    (hmodel : ClassicalGroup.IsPSL (S ⧸ center S) n q) : n ≤ 3 :=
  Nonsemisimple.RankTwoSieve.linear_dimension_le_three
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) hmodel

end CFSG.Quasithin.ChapterA.Section02
