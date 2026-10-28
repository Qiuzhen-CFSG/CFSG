module
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.OriginalSource.SmallCovers
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.OrthogonalCompletion
/-!
# All odd classical Case II branches from the original source

The original counterexample supplies odd center; it need not separately
supply a primary-center identity. Actual central-quotient root bounds reduce
the linear, unitary and symplectic dimensions and field degrees. The small
cover calculations recover any needed cubic-primary center from the
original offending prime. For the orthogonal signs the actual small aliases
and ternary rank-four centralizers finish every catalogue parameter.

These specialized endpoints preserve the earlier Case II statements and
remove their extra primary-center premise for the final ABC induction.
Source: Aschbacher–Smith A.2.17, printed pp.38–39.
-/

public section
open Subgroup Matrix Theory.GroupTheory PerfectCentralCovering BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
universe u
variable {K : GroupClass.{u}} {G S : Type u} [Group G] [Finite G] [Group S] [Finite S]
  [IsQuasisimple G] {p : ℕ}

theorem linear_caseII_parameters_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    {r e n : ℕ} [Fact r.Prime]
    (hn : 2 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPSL (G ⧸ center G) n (r^e)) : n = 4 ∧ e = 1 := by
  have ho := h.center_odd_card ih.theoremA
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  have hn4 := DefiningKernel.linear_degree_le_four_of_odd_center hr2 he h.1 ho model
  have hn2 : n ≠ 2 := by
    intro hn2
    subst n
    obtain ⟨F,hF,hfin,hc,⟨iso⟩⟩ := model
    let : Group.IsPerfect PSL(2,F) :=
      Group.IsPerfect.ofSurjective (f := iso.toMonoidHom) iso.surjective
    have hq : 3 < Nat.card F := by
      by_contra hq
      have hl : 1 < Nat.card F := Finite.one_lt_card
      have hfodd : Odd (Nat.card F) := hc ▸ hr.pow
      have h3 : Nat.card F = 3 := by obtain ⟨k,hk⟩ := hfodd; omega
      exact Matrix.ProjectiveSpecialLinearGroup.not_perfect_of_card_three h3 inferInstance
    exact linear_two_caseII_of_source h ih (hc ▸ hq) hr.pow ⟨F,hF,hfin,hc,⟨iso⟩⟩
  have hn3 : n ≠ 3 := by
    intro hn3
    subst n
    exact linear_three_caseII_of_source h ih hr he model
  have hn4eq : n = 4 := by omega
  subst n
  exact ⟨rfl,linear_four_fieldExponent_eq_one_of_odd_center h.1 ho hr he model⟩

theorem linear_caseII_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    {r e n : ℕ} [Fact r.Prime]
    (hn : 2 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPSL (G ⧸ center G) n (r^e)) : False := by
  obtain ⟨rfl,rfl⟩ := linear_caseII_parameters_of_source h ih hn hr he model
  obtain ⟨F,hF,hfin,hcard,⟨iso⟩⟩ := model
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  have ho := h.center_odd_card ih.theoremA
  let c := PerfectCentralCovering.centralQuotientCover iso
  obtain ⟨s,hs,hfac,_⟩ :=
    Theory.SpecificGroups.LinearHigher.OddCharacteristicCover.exists_covering_of_card_prime
      Fact.out hr2 (by simpa using hcard) c.toMonoidHom c.surjective c.ker_le_center
      (by simpa only [c,PerfectCentralCovering.centralQuotientCover_ker] using ho)
  have hd := kernel_card_dvd_of_surjective_factor
    (QuotientGroup.mk' (center SL(4,F))) c.toMonoidHom s hs hfac
  have hz4 : Nat.card (center G) ∣ 4 := by
    have hk : Nat.card (MonoidHom.ker (QuotientGroup.mk' (center SL(4,F)))) =
        Nat.gcd 4 (Nat.card F - 1) := by
      rw [QuotientGroup.ker_mk',Atlas.ExceptionalSupport.card_sl_center]
      rfl
    rw [hk] at hd
    have hd' : Nat.card (center G) ∣ Nat.gcd 4 (Nat.card F - 1) := by
      simpa only [c,PerfectCentralCovering.centralQuotientCover_ker] using hd
    exact hd'.trans (Nat.gcd_dvd_left _ _)
  have hz1 : Nat.card (center G) = 1 := Nat.eq_one_of_dvd_coprimes
    (ho.coprime_two_right.pow_right 2) dvd_rfl hz4
  exact h.center_ne_bot ih.theoremA ((center G).eq_bot_of_card_eq hz1)

theorem symplectic_caseII_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    {r e n : ℕ} [Fact r.Prime]
    (hn : 1 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPSp (G ⧸ center G) n (r^e)) : False := by
  obtain ⟨F, hF, hfin, hc, ⟨iso⟩⟩ := model
  have ho := h.center_odd_card ih.theoremA
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
    exact linear_two_caseII_of_source h ih (hc ▸ hq) hr.pow ⟨F,hF,hfin,hc,⟨j⟩⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  by_cases h2 : n = 2
  · subst n
    have he1 := Theory.SpecificGroups.Symplectic.OddCentralQuotientRank.fieldExponent_eq_one_of_odd_center
      hr2 he hc iso ho h.1
    subst e
    exact symplectic_prime_caseII_of_source h ih hr
      ⟨F,hF,hfin,by simpa only [pow_one] using hc,⟨iso⟩⟩
  obtain ⟨k,rfl⟩ : ∃ k, n = k+3 := ⟨n-3,by omega⟩
  exact Theory.SpecificGroups.Symplectic.OddCentralQuotientRank.not_quasithin_of_odd_center_higher_model
    hr2 he hc k iso ho h.1

theorem unitary_four_prime_caseII_false_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    {r : ℕ} [Fact r.Prime] (hr : 3 < r)
    (model : ClassicalGroup.IsPSU (G ⧸ center G) 4 r) : False := by
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨iso⟩⟩ := model
  have ho := h.center_odd_card ih.theoremA
  exact h.center_ne_bot ih.theoremA
    (Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddPrimeCover.center_eq_bot_of_quotient_equiv
      J Fact.out hr hcard hconj iso ho)

theorem unitary_caseII_parameters_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    {n r e : ℕ} [Fact r.Prime]
    (hn : 2 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPSU (G ⧸ center G) n (r^e)) :
    4 ≤ n ∧ r = 3 ∧ e = 1 := by
  have hn2 : n ≠ 2 := by
    intro h2
    subst n
    exact linear_caseII_of_source h ih (by decide) hr he
      (model.isPSL_two ((isPrimePow_nat_iff _).mpr ⟨r,e,Fact.out,by omega,rfl⟩))
  have hn3 : n ≠ 3 := by
    intro h3
    subst n
    exact unitary_three_caseII_of_source h ih hr he model
  have hn4 : 4 ≤ n := by omega
  have ho := h.center_odd_card ih.theoremA
  obtain ⟨he1,hnr⟩ := unitary_higher_central_quotient_parameters hn4 hr he ho h.1 model
  refine ⟨hn4,?_,he1⟩
  rcases hnr with hn4 | hr3
  · subst n
    subst e
    by_contra hr3
    have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
    have hrgt : 3 < r := by have := (Fact.out : r.Prime).two_le; omega
    exact unitary_four_prime_caseII_false_of_source h ih hrgt (by simpa only [pow_one] using model)
  · exact hr3

theorem unitary_caseII_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    {n r e : ℕ} [Fact r.Prime]
    (hn : 2 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPSU (G ⧸ center G) n (r^e)) : False := by
  obtain ⟨hn4,rfl,rfl⟩ := unitary_caseII_parameters_of_source h ih hn hr he model
  simp only [pow_one] at model
  by_cases hn : n = 4
  · subst n
    exact unitary_four_three_caseII_of_source h ih model
  obtain ⟨k,hk,rfl⟩ : ∃ k, 0 < k ∧ n = 4+k := ⟨n-4,by omega,by omega⟩
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨iso⟩⟩ := model
  have ho := h.center_odd_card ih.theoremA
  exact Theory.SpecificGroups.ClassicalUnitary.HigherUnitaryTernary.not_quasithin_of_odd_center_quotient
    hk J (by simpa using hcard) hconj iso ho h.1

theorem orthogonal_odd_caseII_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    {n r e : ℕ} [Fact r.Prime] (hn : 1 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPOmegaOdd (G ⧸ center G) n (r^e)) : False := by
  by_cases h1 : n = 1
  · subst n
    exact linear_caseII_of_source h ih (by decide) hr he
      (SmallIsomorphisms.isPSL_two_of_isPOmegaOdd_one model)
  by_cases h2 : n = 2
  · subst n
    exact symplectic_caseII_of_source h ih (by decide) hr he
      (SmallIsomorphisms.isPSp_two_of_isPOmegaOdd_two hr.pow model)
  have hn3 : 3 ≤ n := by omega
  obtain ⟨rfl,rfl⟩ := orthogonal_odd_central_quotient_parameters hn3 hr he
    (h.center_odd_card ih.theoremA) h.1 model
  obtain ⟨F,_,_,hc,⟨iso⟩⟩ := model
  exact ClassicalOrthogonal.OddSevenTernaryCover.not_isQuasithin_of_odd_quotient_equiv
    hn3 (by simpa using hc) iso (h.center_odd_card ih.theoremA) h.1

theorem orthogonal_plus_caseII_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    {n r e : ℕ} [Fact r.Prime] (hn : 3 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPOmegaPlus (G ⧸ center G) n (r^e)) : False := by
  by_cases h3 : n = 3
  · subst n
    exact linear_caseII_of_source h ih (by decide) hr he (model.three_isPSL_four hr.pow)
  have hn4 : 4 ≤ n := by omega
  obtain ⟨rfl,rfl⟩ := orthogonal_plus_central_quotient_parameters hn4 hr he
    (h.center_odd_card ih.theoremA) h.1 model
  obtain ⟨F,_,_,hc,⟨iso⟩⟩ := model
  exact ClassicalOrthogonal.OddSevenTernaryCover.not_isQuasithin_of_plus_quotient_equiv
    hn4 (by simpa using hc) iso (h.center_odd_card ih.theoremA) h.1

theorem orthogonal_minus_caseII_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    {n r e : ℕ} [Fact r.Prime] (hn : 2 ≤ n) (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPOmegaMinus (G ⧸ center G) n (r^e)) : False := by
  by_cases h2 : n = 2
  · subst n
    have hm : ClassicalGroup.IsPSL (G ⧸ center G) 2 (r^(e*2)) := by
      simpa only [pow_mul] using SmallIsomorphisms.isPSL_two_sq_of_isPOmegaMinus_two model
    exact linear_caseII_of_source h ih (by decide) hr (by omega) hm
  by_cases h3 : n = 3
  · subst n
    let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
    exact unitary_caseII_of_source h ih (by decide) hr he
      (SmallIsomorphisms.isPSU_four_of_isPOmegaMinus_three hr.pow model)
  have hn4 : 4 ≤ n := by omega
  obtain ⟨rfl,rfl⟩ := orthogonal_minus_central_quotient_parameters hn4 hr he
    (h.center_odd_card ih.theoremA) h.1 model
  obtain ⟨F,_,_,hc,⟨iso⟩⟩ := model
  exact ClassicalOrthogonal.OddSevenTernaryCover.not_isQuasithin_of_minus_quotient_equiv
    hn4 (by simpa using hc) iso (h.center_odd_card ih.theoremA) h.1

end CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
