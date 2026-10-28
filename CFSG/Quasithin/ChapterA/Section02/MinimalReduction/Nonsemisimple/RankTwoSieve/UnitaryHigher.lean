module
public import Theory.SpecificGroups.ClassicalUnitary.TwoRankLower
public import CFSG.KnownSimple.ClassicalModels
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankReduction
/-!
# Higher unitary exclusions in the original A.2 two-rank sieve

Every literal unitary model in dimension at least four has ordinary two-rank
at least three. The source consumer applies the proved bound on the actual
section central quotient, without assuming that quotient is quasithin.
Source: Aschbacher--Smith A.2.12, printed p.36.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
variable {Q : Type u} [Group Q] [Finite Q]
/-- Every genuine higher unitary model is absent from the two-rank-two list. -/
theorem no_unitary_higher_model (hr : primeRank 2 Q ≤ 2) {d q : ℕ}
    (hd : 4 ≤ d) (hq : IsPrimePow q) (model : ClassicalGroup.IsPSU Q d q) : False := by
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := model
  have hb := Theory.SpecificGroups.ClassicalUnitary.TwoRank.higher_three_le hd J hq hcard hconj
  rw [←primeRank_equiv 2 e] at hb
  omega

/-- The exact full-catalogue parameters supply every field hypothesis. -/
theorem unitary_degree_le_three (hr : primeRank 2 Q ≤ 2) {d q : ℕ}
    (hp : KnownSimple.UnitaryParameters d q) (model : ClassicalGroup.IsPSU Q d q) : d ≤ 3 := by
  by_contra hd
  exact no_unitary_higher_model hr (by omega) hp.1 model
end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p d q : ℕ}
/-- The actual nonsemisimple source quotient has unitary dimension at most three. -/
theorem CounterexampleToTheoremA.centralQuotient_unitary_degree_le_three
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) (hp : KnownSimple.UnitaryParameters d q)
    (model : ClassicalGroup.IsPSU (S ⧸ center S) d q) : d ≤ 3 :=
  Nonsemisimple.RankTwoSieve.unitary_degree_le_three
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) hp model
end CFSG.Quasithin.ChapterA.Section02
