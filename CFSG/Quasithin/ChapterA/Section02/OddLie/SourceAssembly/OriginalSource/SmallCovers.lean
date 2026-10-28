module
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.UnitaryCompletion
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.SymplecticCover
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.PrimeCore.OffendingPrime
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.PrimeCore.UnitaryPairSource
public import Theory.SpecificGroups.PSL2.OddCoverKernel
/-!
# Small odd classical covers from the original counterexample

The original source gives odd center and divisibility by the offending
prime. The genuine scalar-cover bounds therefore recover the required
primary center at the cubic endpoints. At the ordinary linear-two and
prime symplectic endpoints, the actual kernel-two calculation forces the
odd center to be trivial. The retained original Case II theorems then
apply without an independently assumed primary-center hypothesis.
Source: Aschbacher–Smith A.2.14 and A.2.17, printed pp.37–39.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
universe u
variable {K : GroupClass.{u}} {G S : Type u} [Group G] [Finite G] [Group S] [Finite S]
  [IsQuasisimple G] {p : ℕ}

private theorem primary_center_of_three
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hc : Nat.card (center G) = 3) : IsPGroup p (center G) := by
  have h3 : IsPGroup 3 (center G) := IsPGroup.of_card (n := 1) (by simpa using hc)
  exact h.prime_eq_of_center_isPGroup ih h3 ▸ h3

theorem linear_two_caseII_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    {q : ℕ} (hq : 3 < q) (ho : Odd q)
    (model : ClassicalGroup.IsPSL (G ⧸ center G) 2 q) : False := by
  obtain ⟨F, hF, hfin, hcard, ⟨iso⟩⟩ := model
  by_cases h9 : Nat.card F = 9
  · let a := iso.trans (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 h9)
    have hn : Nat.card (center G) ≠ 1 :=
      fun hc => h.center_ne_bot ih.theoremA ((center G).eq_bot_of_card_eq hc)
    obtain ⟨_,hc⟩ := (GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 6
      (by decide) a (h.center_odd_card ih.theoremA)).resolve_left hn
    exact h.not_alternating_centralQuotient ih.theoremA
      (primary_center_of_three h ih.theoremA hc) (by decide : 5 ≤ 6) a
  let : Fact (3 < Nat.card F) := ⟨hcard ▸ hq⟩
  have hd := Theory.PSL2.odd_cover_kernel_card_dvd_two (hcard ▸ ho) h9 (centralQuotientCover iso)
  have hc : Nat.card (center G) ∣ 2 := by simpa only [centralQuotientCover_ker] using hd
  have hz : Nat.card (center G) = 1 := Nat.eq_one_of_dvd_coprimes
    (h.center_odd_card ih.theoremA).coprime_two_right dvd_rfl hc
  exact h.center_ne_bot ih.theoremA ((center G).eq_bot_of_card_eq hz)

theorem linear_three_caseII_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    {r e : ℕ} [Fact r.Prime] (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPSL (G ⧸ center G) 3 (r^e)) : False := by
  obtain ⟨F,hF,hfin,hcard,⟨iso⟩⟩ := model
  have hodd : Odd (Nat.card F) := hcard ▸ hr.pow
  have h2 : Nat.card F ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hodd)
  have h4 : Nat.card F ≠ 4 := fun hh => (by decide : ¬ Odd 4) (hh ▸ hodd)
  obtain ⟨hc,_,_,_⟩ := Matrix.PSL3.OrdinaryCenterRecognition.nontrivial_center_recognition
    h2 h4 iso (h.center_ne_bot ih.theoremA)
  exact linear_three_caseII h ih (primary_center_of_three h ih.theoremA hc) hr he
    ⟨F,hF,hfin,hcard,⟨iso⟩⟩

theorem unitary_three_caseII_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    {r e : ℕ} [Fact r.Prime] (hr : Odd r) (he : 1 ≤ e)
    (model : ClassicalGroup.IsPSU (G ⧸ center G) 3 (r^e)) : False := by
  have he2 := unitary_three_fieldExponent_le_two_of_central_quotient hr he h.1 model
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨iso⟩⟩ := model
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  obtain ⟨hc,_⟩ := HermitianForm.OddCenterRecognition.nontrivial_center_card
    J Fact.out hr2 he he2 hcard hconj iso (h.center_odd_card ih.theoremA)
      (h.center_ne_bot ih.theoremA)
  exact unitary_three_caseII h ih (primary_center_of_three h ih.theoremA hc) hr he
    ⟨F,hF,hfin,J,hcard,hconj,⟨iso⟩⟩

theorem unitary_four_three_caseII_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (model : ClassicalGroup.IsPSU (G ⧸ center G) 4 3) : False := by
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨iso⟩⟩ := model
  obtain ⟨hE,_⟩ :=
    Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddPrimeCover.center_elementary_three_and_card_dvd_nine
      J (by simpa using hcard) hconj iso (h.center_odd_card ih.theoremA)
  let := hE
  have h3 := IsElementaryAbelian.isPGroup 3 (center G)
  have hP : IsPGroup p (center G) := h.prime_eq_of_center_isPGroup ih.theoremA h3 ▸ h3
  exact unitary_four_three_caseII h ih hP ⟨F,hF,hfin,J,hcard,hconj,⟨iso⟩⟩

theorem symplectic_prime_caseII_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    {r : ℕ} [Fact r.Prime] (hr : Odd r)
    (model : ClassicalGroup.IsPSp (G ⧸ center G) 2 r) : False := by
  obtain ⟨F, hF, hfin, hc, ⟨iso⟩⟩ := model
  let : Fact (2 < Nat.card F) := ⟨by
    have := (Fact.out : r.Prime).two_le
    have hne : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
    omega⟩
  let c := centralQuotientCover iso
  let d : Covering G (ClassicalGroup.PSp 2 F) := c.toCovering
  have hr2 : r ≠ 2 := fun hh => (by decide : ¬ Odd 2) (hh ▸ hr)
  have hu := Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.quotientCover_isUniversal hr2 hc
  have hfac : c.toMonoidHom.comp (hu.lift d).toMonoidHom =
      (Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.quotientCover F).toMonoidHom :=
    congrArg Covering.toMonoidHom (hu.lift_fac d)
  have hdvd : Nat.card (center G) ∣ 2 := by
    have hd := kernel_card_dvd_of_surjective_factor
      (Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.quotientCover F).toMonoidHom
      c.toMonoidHom (hu.lift d).toMonoidHom (hu.lift d).surjective hfac
    have hk : Nat.card
        (Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.quotientCover F).toMonoidHom.ker = 2 := by
      rw [show (Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.quotientCover F).toMonoidHom.ker = center (Matrix.symplecticGroup (Fin 2) F) from QuotientGroup.ker_mk' _]
      exact Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.card_center
        (Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.two_ne_zero Fact.out hr2 hc)
    simpa only [hk, c, centralQuotientCover_ker] using hd
  have hcard1 : Nat.card (center G) = 1 := Nat.eq_one_of_dvd_coprimes
    (h.center_odd_card ih.theoremA).coprime_two_right dvd_rfl hdvd
  exact h.center_ne_bot ih.theoremA ((center G).eq_bot_of_card_eq hcard1)

end CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
