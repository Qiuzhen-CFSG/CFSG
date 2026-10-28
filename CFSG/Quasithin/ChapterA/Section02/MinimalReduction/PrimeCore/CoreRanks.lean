module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.PrimeCore.OddCore
public import CFSG.Quasithin.ChapterA.Section01.SectionRank

/-!
# A.1.28 applied to the literal A.2 minimal counterexample

The odd-core quotient has trivial center by the marked semisimple covering.
The full equality clause of A.1.28 therefore improves its two-rank bound
from three to two. Conversely, two-rank at least three bounds every odd
prime core's rank by two. No quotient-quasithinness premise is used.

Source: Aschbacher–Smith A.2.11–12, printed pp.35–36.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
    [Group G] [Group S] [Finite G] [Finite S] {p q : ℕ}

theorem CounterexampleToTheoremA.twoRank_le_two_of_large_primeCore
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    [Fact q.Prime] (hq : Odd q) (hr : 2 < primeRank q (pCore q G)) :
    primeRank 2 G ≤ 2 := by
  have hl := isQuasithin_iff_twoLocalPrimeRank.mp h.1 q Fact.out hq
  obtain ⟨hb, hz⟩ := lemma_A_1_28_group hq hl hr
  have hn : primeRank 2 G ≠ 3 := fun he =>
    hz he (h.center_oddCore_quotient_eq_bot ih)
  omega

theorem CounterexampleToTheoremA.primeCore_rank_le_two_of_three_le_twoRank
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    [Fact q.Prime] (hq : Odd q) (hr : 3 ≤ primeRank 2 G) :
    primeRank q (pCore q G) ≤ 2 :=
  lemma_A_1_28_core_rank_le_two_of_center_oddCore_eq_bot hq
    (isQuasithin_iff_twoLocalPrimeRank.mp h.1 q Fact.out hq) hr
    (h.center_oddCore_quotient_eq_bot ih)

end CFSG.Quasithin.ChapterA.Section02
