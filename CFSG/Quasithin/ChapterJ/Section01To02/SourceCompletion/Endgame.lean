module

public import CFSG.Quasithin.ChapterJ.Section01To02.SourceCompletion.CubicSource
public import CFSG.Quasithin.ChapterJ.Section01To02.SourceCompletion.Five
public import CFSG.Quasithin.ChapterJ.Section01To02.SourceCompletion.Odd
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Counting.Transitivity

/-!
# The original J.1–2 family used by the order argument

For every original local setup and its actual choices, all fusion inputs,
the two involution classes, the Suzuki centralizer, the middle count480,
the cubic Sylow of order27, and the five-centralizer of order1000 are proved.
The accompanying imports expose the marked triple cover and every J.2.10
odd-prime normalizer conclusion with their original quotient maps.

This assembles the source family required by J.3 and the corrected
H-transitivity assertion of J.2.7(8) on the same original middle set.

Source: Aschbacher–Smith, J.1–2, printed pp.431–438.
-/

public section
namespace CFSG.Quasithin.ChapterJ.SourceCompletion
open Subgroup Centralizers Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} (c:Choices d)

/-- The corrected source orbit statement and its exact middle count. -/
theorem source_J_2_7_eight :
    Fusion.TransitiveOn d.toTypeRuSetup.H
      {x:G | IsConj c.z x ∧ x∈d.toTypeRuSetup.K ∧ x∉d.toTypeRuSetup.Q} ∧
    Nat.card {x:G // IsConj c.z x ∧ x∈d.toTypeRuSetup.K ∧ x∉d.toTypeRuSetup.Q}=480 :=
  c.middle_z_class_orbit_source

/-- The complete original-source family consumed by the J.3 order proof. -/
theorem endgame_source :
    Fusion.SourceJ24 d.toTypeRuSetup ∧
      Fusion.SourceJ25 d.toTypeRuSetup c.sylowThree ∧
      Fusion.SourceJ26 d.toTypeRuSetup c.z ∧
      Fusion.SourceJ28 d.toTypeRuSetup c.z ∧
      ChapterA.Section05To06.TwoInvolutionClasses c.z c.s ∧
      Nonempty c.SuzukiSourceConclusion ∧
      Nat.card {x:G // IsConj c.z x ∧ x∈d.toTypeRuSetup.K ∧ x∉d.toTypeRuSetup.Q}=480 ∧
      (∃ P:Sylow 3 G,Nat.card P=27 ∧ IsExtraspecial 3 P ∧ Monoid.exponent P=3) ∧
      ∀ B5:Sylow 5 d.toTypeRuSetup.H,
        G5 B5=pCoreIn 5 (G5 B5)⊔CQ B5 ∧ Nonempty (CQ B5≃*QuaternionGroup 2) ∧
          Nat.card (pCoreIn 5 (G5 B5))=125 ∧ NotConjToLB c B5 := by
  obtain ⟨P,hcard,hexp,horder,_⟩ := cubic_sylow_source c
  have hf := fusion c
  exact ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2,c.two_involution_classes_source,
    c.suzuki_source,c.middle_z_class_card_source,
    ⟨P,hcard,hexp,horder⟩,five_core_source c⟩

/-- Every group of type Ru supplies the actual earlier-source package for J.3. -/
theorem exists_endgame_source (h:IsTypeRu G) :
    ∃ (d:LocalSetup G) (c:Choices d),
      Fusion.SourceJ26 d.toTypeRuSetup c.z ∧ Fusion.SourceJ28 d.toTypeRuSetup c.z ∧
      ChapterA.Section05To06.TwoInvolutionClasses c.z c.s ∧
      Nonempty c.SuzukiSourceConclusion ∧
      Nat.card {x:G // IsConj c.z x ∧ x∈d.toTypeRuSetup.K ∧ x∉d.toTypeRuSetup.Q}=480 ∧
      (∃ P:Sylow 3 G,Nat.card P=27) ∧
      ∃ P:Subgroup G,Nat.card P=125 := by
  obtain ⟨d⟩ := h.nonempty_localSetup
  obtain ⟨c⟩ := exists_choices d
  obtain ⟨_,_,h26,h28,hclasses,hsuzuki,h480,h3,h5⟩ := endgame_source c
  obtain ⟨P,hP,_⟩ := h3
  let B5:Sylow 5 d.toTypeRuSetup.H := Classical.choice inferInstance
  exact ⟨d,c,h26,h28,hclasses,hsuzuki,h480,⟨P,hP⟩,
    pCoreIn 5 (G5 B5),(h5 B5).2.2.1⟩

end CFSG.Quasithin.ChapterJ.SourceCompletion
