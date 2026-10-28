module
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.SmallQuotients
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.LinearTwoLocalRank
public import Theory.SpecificGroups.PSL2.OddCoverKernel
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360
/-!
# Closing the original odd PSL₂ quotient branch

The universal kernel bound excludes a nontrivial perfect central p-cover
at the original odd offending prime. The nilpotent-kernel extraction then
forces the original local-rank failure to survive in S/Z(S). The concrete
PSL₂ local bound contradicts it. At field order nine the actual A₆
comparison instead applies the completed small-cover ordinary-rank bound.

This discharges both possible clauses of the original Theorem A failure;
no prime-core identity or quotient quasithinness is assumed.
Source: Aschbacher–Smith A.2.12, printed p.36.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
    [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

theorem CounterexampleToTheoremA.not_odd_psl_two_centralQuotient
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (hn : ¬ IsSemisimple G) {q : ℕ} (hq3 : 3 < q)
    (hq : GorensteinWalter.IsOddPrimePower q)
    (model : ClassicalGroup.IsPSL (S ⧸ center S) 2 q) : False := by
  have hlocal := h.centralQuotient_odd_psl_two_localRank_le_two hq model
  obtain ⟨F, _, _, hcard, ⟨a⟩⟩ := model
  by_cases h9 : Nat.card F = 9
  · exact h.not_small_alternating_centralQuotient ih hn 6 (by decide) (by decide)
      (a.trans (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 h9))
  let : Fact (3 < Nat.card F) := ⟨hcard ▸ hq3⟩
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    obtain ⟨r,e,_,ho,_,rfl⟩ := hq
    exact ho.pow
  apply (not_le_of_gt (h.centralQuotient_local_rank_gt_two_of_no_prime_cover ih.theoremA ?_)) hlocal
  intro L _ _ c
  let d : Cover L PSL(2,F) :=
    { toMonoidHom := a.toMonoidHom.comp c.toMonoidHom
      surjective := a.surjective.comp c.surjective
      isPerfect := c.isPerfect
      ker_le_center := by
        intro x hx
        apply c.ker_le_center
        exact a.injective (by simpa using hx) }
  have hk : d.toMonoidHom.ker = c.toMonoidHom.ker :=
    MonoidHom.ker_comp_of_injective c.toMonoidHom a.toMonoidHom a.injective
  intro hd
  have hd2 : p ∣ 2 := (hk ▸ hd).trans (Theory.PSL2.odd_cover_kernel_card_dvd_two hodd h9 d)
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq h.2.2.2.2.1 Nat.prime_two).mp hd2
  have ho := h.2.2.2.2.2.1
  rw [hp2] at ho
  norm_num at ho

end CFSG.Quasithin.ChapterA.Section02
