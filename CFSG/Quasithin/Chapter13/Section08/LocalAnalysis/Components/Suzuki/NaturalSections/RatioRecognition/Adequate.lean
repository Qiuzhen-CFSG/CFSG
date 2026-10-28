module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.RatioRecognition.FFExclusion
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.Adequate

/-!
# Ratio recognition from the adequate FF classification

The order argument in the Suzuki natural-section consumer uses only the
actual factor equivalences.  In the outer branch this is precisely the
`A₆ × C₃` group shape, so it does not need the disputed representation
splitting.  The theorem names are suffixed `_of_adequate`; the older full
`SourceAlternative` conclusions remain unchanged.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition
universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

theorem three_dvd_card_adequate_nonQuasisimple [Finite D]
    (h : AdequateNonQuasisimpleAlternative ρ) : 3 ∣ Nat.card D := by
  cases h with
  | symmetricThree c =>
    rw [Nat.card_congr c.equiv.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  | twoFactors c =>
    exact (three_dvd_card_factorModel (c.firstCase.factorModel _)).trans
      c.first.card_subgroup_dvd_card
  | outerSixThree c =>
    have hc : Nat.card c.second = 3 :=
      (Nat.card_congr c.secondEquiv.toEquiv).trans (Nat.card_zmod 3)
    exact hc ▸ c.second.card_subgroup_dvd_card
  | hyperplane c =>
    have hc : 3 ∣ Nat.card c.first := by
      rw [Nat.card_congr c.firstEquiv.toEquiv]
      exact Theory.SpecificGroups.three_dvd_card_sl_three (ZMod 2)
    exact hc.trans c.first.card_subgroup_dvd_card

theorem three_dvd_card_adequate_sourceAlternative [Finite D]
    (h : AdequateSourceAlternative ρ) (hff : IsFFModule ρ) :
    3 ∣ Nat.card D := by
  rcases h.groupCases_of_ff ρ hff with ⟨hq, hm⟩ | h
  · let := hq
    exact (three_dvd_card_quasisimpleModel hm).trans
      (generalizedFitting D).card_subgroup_dvd_card
  · exact three_dvd_card_adequate_nonQuasisimple ρ h

theorem not_ff_of_three_free_of_adequate [Finite D] [Module.Finite (ZMod 2) V]
    {K : GroupClass.{u}} (classification : AdequateCompleteClassificationInput.{u,v} K)
    (hfaith : Function.Injective ρ) (h₂ : pCore 2 D = ⊥)
    (hcover : Nonempty (SQTKQuotient K D)) (hthree : ¬ 3 ∣ Nat.card D) :
    ¬ IsFFModule ρ := by
  intro hff
  have h := classification.general (offenderSubgroup ρ) V
    (ρ.comp (offenderSubgroup ρ).subtype)
    (offender_restriction_hypothesis ρ hfaith h₂ hcover)
  exact hthree ((three_dvd_card_adequate_sourceAlternative _ h
    (offender_restriction_ff ρ hff)).trans
    (offenderSubgroup ρ).card_subgroup_dvd_card)

theorem not_strongFF_of_three_free_of_adequate [Finite D]
    [Module.Finite (ZMod 2) V] {K : GroupClass.{u}}
    (classification : AdequateCompleteClassificationInput.{u,v} K)
    (hfaith : Function.Injective ρ) (h₂ : pCore 2 D = ⊥)
    (hcover : Nonempty (SQTKQuotient K D)) (hthree : ¬ 3 ∣ Nat.card D) :
    ¬ IsStrongFFModule ρ := by
  rintro ⟨A, hA, hlt⟩
  exact not_ff_of_three_free_of_adequate ρ classification hfaith h₂ hcover hthree
    ⟨A, hA, hlt.le⟩

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition
