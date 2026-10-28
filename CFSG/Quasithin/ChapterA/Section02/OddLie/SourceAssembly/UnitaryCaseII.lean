module
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.UnitaryHigherCover
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.LinearCover
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddPrimeCover

/-!
# The remaining ternary unitary source alternative

All odd unitary central quotients in original Case II reduce to a prime
field and degree at least four. The actual prime-degree covering-kernel
calculation excludes PSU₄ at primes greater than three. Combined with
the ordinary root obstruction in higher degrees, only q = 3 remains.
Source: Aschbacher–Smith A.2.17, printed p.39.
-/

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
universe u
variable {K : GroupClass.{u}} {G S : Type u} [Group G] [Finite G] [Group S] [Finite S]
  [IsQuasisimple G] {p : ℕ}

public theorem unitary_four_prime_caseII_false
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (hP : IsPGroup p (center G)) {r : ℕ} [Fact r.Prime] (hr : 3 < r)
    (model : ClassicalGroup.IsPSU (G ⧸ center G) 4 r) : False := by
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨iso⟩⟩ := model
  have ho : Odd (Nat.card (center G)) := by
    let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
    obtain ⟨k,hk⟩ := hP.exists_card_eq
    rw [hk]
    exact h.2.2.2.2.2.1.pow
  exact h.center_ne_bot ih.theoremA
    (Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddPrimeCover.center_eq_bot_of_quotient_equiv
      J Fact.out hr hcard hconj iso ho)

public theorem unitary_caseII_parameters
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (hP : IsPGroup p (center G)) {n r e : ℕ} [Fact r.Prime]
    (hn : 2 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPSU (G ⧸ center G) n (r^e)) :
    4 ≤ n ∧ r = 3 ∧ e = 1 := by
  have hn2 : n ≠ 2 := by
    intro h2
    subst n
    exact linear_caseII h ih hP (by decide) hr he
      (model.isPSL_two ((isPrimePow_nat_iff _).mpr ⟨r,e,Fact.out,by omega,rfl⟩))
  have hn3 : n ≠ 3 := by
    intro h3
    subst n
    exact unitary_three_caseII h ih hP hr he model
  have hn4 : 4 ≤ n := by omega
  have ho : Odd (Nat.card (center G)) := by
    let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
    obtain ⟨k,hk⟩ := hP.exists_card_eq
    rw [hk]
    exact h.2.2.2.2.2.1.pow
  obtain ⟨he1,hnr⟩ := unitary_higher_central_quotient_parameters hn4 hr he ho h.1 model
  refine ⟨hn4,?_,he1⟩
  rcases hnr with hn4 | hr3
  · subst n
    subst e
    by_contra hr3
    have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
    have hrgt : 3 < r := by have := (Fact.out : r.Prime).two_le; omega
    exact unitary_four_prime_caseII_false h ih hP hrgt (by simpa only [pow_one] using model)
  · exact hr3
end CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
