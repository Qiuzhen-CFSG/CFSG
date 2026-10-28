module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.ModelComparison.Catalogue
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.Adequate.Components
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.SourceB5.Complete

/-!
# Component models from the corrected adequate FF classification

Each ordinary component has one of the actual FF group models. The outer
A₆–C₃ row uses only its group configuration: every component lies in the
specified A₆ factor. In the other rows the existing component catalogue
applies to the unchanged factors. The corrected projective-line convention
is retained throughout. Every resulting component has order divisible by
three, by its proved trivial three-prime core and nontriviality.

The Chapter 13 two-orbit comparison applies this to the original offender
restriction of the W_K action. No whole-space splitting or old full outer
classification implication is assumed.

Source: Aschbacher–Smith B.5.6, printed p.105; 13.6.14, printed p.929.
-/

public section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.ModelComparison.Catalogue

variable {D V : Type*} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

omit [Finite D] in
/-- The adequate outer group contributes its actual alternating-six factor. -/
theorem outer_shape_component_model (c : ChapterB.OuterSixThreeShape D)
    {C : Subgroup D} (hC : IsComponent D C) : QuasisimpleModel C := by
  have hle := outerSixThreeShape_component_le_first c hC
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple (alternatingGroup (Fin 6)) := {
    toIsPerfect := inferInstance
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple c.first := IsQuasisimple.of_mulEquiv c.firstEquiv.symm
  have ht : IsComponent c.first ⊤ :=
    ⟨IsSubnormal.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩
  have he : C = c.first := le_antisymm hle
    (subgroupOf_eq_top.mp ((hC.subgroupOf hle).eq_of_le ht le_top))
  exact .alternatingSix ((MulEquiv.subgroupCongr he).trans c.firstEquiv)

/-- Every component in the corrected adequate alternatives has an actual
FF model; the actor is not assumed perfect. -/
theorem component_model_of_adequate_alternative
    (h : ProjectiveLine.AdequateSourceAlternative ρ)
    {C : Subgroup D} (hC : IsComponent D C) : QuasisimpleModel C := by
  cases h with
  | trivial ht =>
    let := ht
    exact (hC.isCComponent.ne_bot (Subsingleton.elim _ _)).elim
  | quasisimple hq ha =>
    have hf : IsComponent D (generalizedFitting D) :=
      ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal, hq⟩
    have he := hC.eq_of_le hf (component_le_generalizedFitting D C hC)
    exact quasisimpleModel_of_equiv (MulEquiv.subgroupCongr he) (ha.fittingModel ρ)
  | symmetricThree c =>
    exact component_model_of_source_alternative ρ (.symmetricThree c) hC
  | twoFactors c =>
    exact component_model_of_product c.product.equiv.symm
      (c.firstCase.factorModel ρ) (c.secondCase.factorModel ρ) hC
  | outerSixThree c => exact outer_shape_component_model c hC
  | hyperplane c =>
    exact component_model_of_product c.product.equiv.symm
      (.linearThree BinaryField.two (by decide) c.firstEquiv) (c.secondCase.factorModel ρ) hC

/-- The native B.5 classification has the same component catalogue, with
the native action and all quotient maps unchanged. -/
theorem component_model_of_native_alternative
    (h : ChapterB.SourceInduction.AdequateAlternative ρ)
    {C : Subgroup D} (hC : IsComponent D C) : QuasisimpleModel C :=
  component_model_of_adequate_alternative ρ (SourceB5.alternative h) hC

/-- Three divides the order of every quasisimple FF model. This also
excludes the Suzuki row in a separate nonnormal-component catalogue. -/
theorem three_dvd_card_of_quasisimpleModel {X : Type*} [Group X] [Finite X]
    [IsQuasisimple X] (h : QuasisimpleModel X) : 3 ∣ Nat.card X := by
  let : IsSimpleGroup (X ⧸ center X) := IsQuasisimple.simple
  let : Nontrivial X := (QuotientGroup.mk'_surjective (center X)).nontrivial
  have hcore := h.threePrimeCore_eq_bot_of_binaryDerived_center
    (fun _ => Theory.SpecificGroups.g2_derived_two_center_isThreeGroup)
  by_contra hn
  have htop : (⊤ : Subgroup X) ≤ pPrimeCore 3 X :=
    le_sSup ⟨inferInstance, by simpa using Nat.prime_three.coprime_iff_not_dvd.mpr hn⟩
  rw [hcore] at htop
  exact top_ne_bot (top_le_iff.mp htop).symm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.ModelComparison.Catalogue
