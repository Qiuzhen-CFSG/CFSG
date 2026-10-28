module
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.LinearTwo
/-!
# Source contradiction for every survivor of the two-rank sieve

Each literal small or rank-one/two classical survivor is excluded using
the original counterexample and proper-section induction. The ordinary
rank clause and possible central p-kernel have already been discharged
in those source theorems. The separate full known-carrier sieve supplies
exactly the six-way model disjunction consumed here.
Source: Aschbacher–Smith A.2.12(I), printed p.36.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
    [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

theorem CounterexampleToTheoremA.rankTwoSurvivors_false
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (hn : ¬ IsSemisimple G)
    (hm : (∃ q, 3 < q ∧ GorensteinWalter.IsOddPrimePower q ∧
        ClassicalGroup.IsPSL (S ⧸ center S) 2 q) ∨
      (∃ q, GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSL (S ⧸ center S) 3 q) ∨
      (∃ q, GorensteinWalter.IsOddPrimePower q ∧ ClassicalGroup.IsPSU (S ⧸ center S) 3 q) ∨
      Nonempty (S ⧸ center S ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (S ⧸ center S ≃* Sporadic.Mathieu.M11) ∨
      ClassicalGroup.IsPSU (S ⧸ center S) 3 4) : False := by
  rcases hm with ⟨q,hq3,hq,hm⟩ | ⟨q,hq,hm⟩ | ⟨q,hq,hm⟩ | ⟨a⟩ | ⟨a⟩ | hm
  · exact h.not_odd_psl_two_centralQuotient ih hn hq3 hq hm
  · obtain ⟨r,e,hr,ho,he,rfl⟩ := hq
    exact h.not_odd_psl_three_centralQuotient ih r e hr ho (by omega) hm
  · obtain ⟨r,e,hr,ho,he,rfl⟩ := hq
    exact h.not_odd_psu_three_centralQuotient ih hn r e hr ho (by omega) hm
  · obtain ⟨a⟩ := a
    exact h.not_small_alternating_centralQuotient ih hn 7 (by decide) (by decide) a
  · obtain ⟨a⟩ := a
    exact h.not_m11_centralQuotient ih hn a
  · exact h.not_unitary_four_centralQuotient ih hn hm

end CFSG.Quasithin.ChapterA.Section02
