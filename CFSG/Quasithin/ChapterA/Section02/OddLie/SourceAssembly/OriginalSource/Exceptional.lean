module
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.G2Cover
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.Triality
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.Exceptional
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.PrimeCore.OffendingPrime
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.PrimeCore.UnitaryPairSource
/-!
# Remaining rank-two and Ree/F₄ odd source covers

The ternary G₂ multiplier bound and original offending prime recover its
primary center, so the already proved exact Theorem A contradiction applies.
For larger G₂ parameters the original odd center supplies the root-rank
reduction. The complete Ree, F₄ and triality odd-cover obstructions consume
that same source odd-center theorem directly. No primary-center premise is
left in these source endpoints.
Source: Aschbacher–Smith A.2.17, printed p.39.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
universe u
variable {K : GroupClass.{u}} {G S : Type u} [Group G] [Finite G] [Group S] [Finite S]
  [IsQuasisimple G] {p : ℕ}

theorem g2_three_caseII_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (model : ClassificationModels.IsG2At (G ⧸ center G) 3) : False := by
  obtain ⟨F, hF, hfin, hq, ⟨e⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let eF : ZMod 3 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_three (by
    simpa only [Nat.card_eq_fintype_card] using hq)
  let iso := e.trans (Atlas.G2.fieldEquiv eF.symm)
  let : Fact (2 < Nat.card (ZMod 3)) := ⟨by norm_num⟩
  let c := centralQuotientCover iso
  let d : Covering G (Atlas.G2.Model (ZMod 3)) := c.toCovering
  let hu := Atlas.G2.FiniteCover.cover_isUniversal (ZMod 3)
  have hfac : c.toMonoidHom.comp (hu.lift d).toMonoidHom =
      (Atlas.G2.FiniteCover.cover (ZMod 3)).toMonoidHom :=
    congrArg Covering.toMonoidHom (hu.lift_fac d)
  have hd := kernel_card_dvd_of_surjective_factor
    (Atlas.G2.FiniteCover.cover (ZMod 3)).toMonoidHom c.toMonoidHom
    (hu.lift d).toMonoidHom (hu.lift d).surjective hfac
  change Nat.card c.toMonoidHom.ker ∣ Nat.card
    (universalProjection (Atlas.G2.Model (ZMod 3))).ker at hd
  have hd' : Nat.card (center G) ∣ Nat.card (Atlas.G2.FiniteCover.Kernel (ZMod 3)) := by
    simpa only [c, centralQuotientCover_ker] using hd
  have hle : Nat.card (center G) ≤ 3 :=
    (Nat.le_of_dvd Nat.card_pos hd').trans
      Atlas.G2.FiniteCover.MultiplierThree.kernel_card_le_three
  let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
  have ho := h.center_odd_card ih.theoremA
  have hz : Nat.card (center G) = 3 := by
    have hne : Nat.card (center G) ≠ 1 :=
      fun hh => h.center_ne_bot ih.theoremA ((center G).eq_bot_of_card_eq hh)
    have hn0 := Nat.card_pos (α := center G)
    have hh := ho.not_two_dvd_nat
    omega
  have h3 : IsPGroup 3 (center G) := IsPGroup.of_card (n := 1) (by simpa using hz)
  have hP : IsPGroup p (center G) := h.prime_eq_of_center_isPGroup ih.theoremA h3 ▸ h3
  exact g2_three_caseII h ih hP ⟨F,hF,hfin,hq,⟨e⟩⟩

theorem g2_caseII_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    {r e : ℕ} [Fact r.Prime] (hr : Odd r) (he : 1 ≤ e)
    (model : ClassificationModels.IsG2At (G ⧸ center G) (r^e)) : False := by
  have he1 := g2_fieldExponent_eq_one_of_odd_center h.1 (h.center_odd_card ih.theoremA) hr he model
  subst e
  simp only [pow_one] at model
  by_cases h3 : r = 3
  · subst r
    exact g2_three_caseII_of_source h ih model
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  have hgt : 3 < r := by have := (Fact.out : r.Prime).two_le; omega
  exact g2_large_prime_caseII h ih hgt model

theorem ree_caseII_false_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G) {q : ℕ}
    (model : ExceptionalGroup.IsReeG2 (G ⧸ center G) q) : False := by
  obtain ⟨m,F,hF,hfin,hchar,hp,_,⟨iso⟩⟩ := model
  exact ReeOddCover.not_quasithin_of_centralQuotientEquiv m hp.positive hp.cardinality
    iso (h.center_odd_card ih.theoremA) h.1

omit [IsQuasisimple G] in
theorem f4_caseII_false_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    {r e : ℕ} [Fact r.Prime] (hr : Odd r)
    (model : ExceptionalGroup.IsF4 (G ⧸ center G) (r^e)) : False := by
  obtain ⟨F,hF,hfin,hcard,⟨iso⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  exact F4OddCover.not_quasithin_of_odd_center hr2 hcard iso (h.center_odd_card ih.theoremA) h.1

omit [IsQuasisimple G] in
theorem triality_caseII_false_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (P : Triality.Standard.Parameters) (hp : Odd P.prime)
    (iso : G ⧸ center G ≃* Triality.Standard.Carrier P) : False := by
  exact DefiningKernel.not_quasithin_triality_cover hp
    (Triality.Standard.OddFundamentalCentralizer.RankOne.pinnedRankOneMaps P)
    (Triality.Standard.OddFundamentalCentralizer.RankOne.armRootCommutation P)
    (Triality.Standard.OddFundamentalCentralizer.RankOne.fundamentalHom_injective P hp)
    (Triality.Standard.OddFundamentalCentralizer.RankOne.complementHom_injective P hp)
    (Triality.Standard.OddFundamentalCentralizer.fundamentalHom_complementHom_commute _ _)
    iso (h.center_odd_card ih.theoremA) h.1

end CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
