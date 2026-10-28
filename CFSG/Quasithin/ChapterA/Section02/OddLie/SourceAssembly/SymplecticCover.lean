module
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.PrimeCovers
public import Theory.SpecificGroups.Symplectic.OddCentralQuotientRank
public import Theory.SpecificGroups.SL2.SmallOddComparisons

/-!
# Complete odd symplectic source Case II

The literal central quotient has rank-four elementary subgroups in scalar
involution centralizers above symplectic rank two. Rank two over an extension
field has the same obstruction. Thus the actual odd central cover of a
quasithin group is reduced to prime-field PSp₄, whose proved universal double
cover makes its odd center trivial. Rank one transports to the earlier PSL₂
cover branch; perfectness excludes the three-element solvable endpoint.

This proves the original Case II contradiction from the full Theorem A
counterexample and proper-section induction, with no quotient quasithinness
or unproved multiplier premise.
Source: Aschbacher–Smith A.2.17, printed p.39; I.1.4, printed p.408.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
universe u
variable {K : GroupClass.{u}} {G S : Type u} [Group G] [Finite G] [Group S] [Finite S]
  [IsQuasisimple G] {p : ℕ}

/-- Every odd symplectic central quotient is excluded from original source
Case II. The rank-four block witnesses supply the dimension and field-degree
reductions before the actual universal double cover removes the endpoint. -/
public theorem symplectic_caseII
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (hP : IsPGroup p (center G)) {r e n : ℕ} [Fact r.Prime]
    (hn : 1 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPSp (G ⧸ center G) n (r^e)) : False := by
  obtain ⟨F, hF, hfin, hc, ⟨iso⟩⟩ := model
  have ho : Odd (Nat.card (center G)) := by
    let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    rw [hk]
    exact h.2.2.2.2.2.1.pow
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  by_cases h1 : n = 1
  · subst n
    let j := iso.trans Theory.SpecificGroups.SymplecticRoot.rankOneProjectiveEquiv
    let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      Group.IsPerfect.ofSurjective (f := j.toMonoidHom) j.surjective
    have hq : 3 < Nat.card F := by
      by_contra hq
      have hl : 1 < Nat.card F := Finite.one_lt_card
      have hfodd : Odd (Nat.card F) := hc ▸ hr.pow
      have h3 : Nat.card F = 3 := by obtain ⟨k,hk⟩ := hfodd; omega
      exact Matrix.ProjectiveSpecialLinearGroup.not_perfect_of_card_three h3 inferInstance
    exact linear_two_caseII h ih hP (hc ▸ hq) hr.pow ⟨F,hF,hfin,hc,⟨j⟩⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  by_cases h2 : n = 2
  · subst n
    have he1 := Theory.SpecificGroups.Symplectic.OddCentralQuotientRank.fieldExponent_eq_one_of_odd_center
      hr2 he hc iso ho h.1
    subst e
    exact symplectic_prime_caseII h ih hP hr
      ⟨F,hF,hfin,by simpa only [pow_one] using hc,⟨iso⟩⟩
  obtain ⟨k,rfl⟩ : ∃ k, n = k+3 := ⟨n-3,by omega⟩
  exact Theory.SpecificGroups.Symplectic.OddCentralQuotientRank.not_quasithin_of_odd_center_higher_model
    hr2 he hc k iso ho h.1
end CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
