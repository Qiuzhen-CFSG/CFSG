module
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.OrthogonalOdd
public import Theory.SpecificGroups.ClassicalOrthogonal.TwoRankLower.Plus

/-!
# Excluding the complete split orthogonal family

The literal carrier contains an elementary eight in every catalogue rank.
This discharges the split orthogonal branch of A.2.12, printed p.36, on the
original source quotient S/Z(S).
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
variable {Q : Type u} [Group Q] [Finite Q]

theorem no_orthogonal_plus_model (hr : primeRank 2 Q ≤ 2) {r q : ℕ}
    (hd : 3 ≤ r) (hm : ClassicalGroup.IsPOmegaPlus Q r q) : False := by
  obtain ⟨F,hF,hfin,_,⟨a⟩⟩ := hm
  have hb := ClassicalOrthogonal.TwoRank.plus_three_le (F:=F) hd
  rw [← primeRank_equiv 2 a] at hb
  omega
end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}
theorem CounterexampleToTheoremA.centralQuotient_no_orthogonal_plus_model
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) {r q : ℕ} (hd : 3 ≤ r)
    (hm : ClassicalGroup.IsPOmegaPlus (S ⧸ center S) r q) : False :=
  Nonsemisimple.RankTwoSieve.no_orthogonal_plus_model
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) hd hm
end CFSG.Quasithin.ChapterA.Section02
