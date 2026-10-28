module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.SourceB42

/-!
# Keeping the natural action while inspecting the full B.4.2 list

The group-only projection of B.4.2 forgets the natural-module coordinates.
Here we retain those coordinates in the SL₃ case and keep every other
component model, including both small derived endpoints and the triple
cover. No nonisomorphism or classification result is assumed by the split.
The remaining model comparisons must eliminate its second alternative.

Source: Aschbacher–Smith, B.4.2, printed p.86, used in the proof of
13.8.20, printed pp.954–955.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo

open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong

universe u v

/-- Every B.4.2 component possibility apart from its natural SL₃ case.
These are actual group comparisons, with the exceptional center retained. -/
inductive OtherModel (L : Type*) [Group L] : Prop
  | linearTwo (F : BinaryField) (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier)
  | symplecticFour (F : BinaryField) (e : L ≃* Matrix.symplecticGroup (Fin 2) F.Carrier)
  | g2 (F : BinaryField) (e : L ≃* Atlas.G2.Model F.Carrier)
  | g2DerivedTwo (e : L ≃* commutator (Atlas.G2.Model (ZMod 2)))
  | alternatingSix (e : L ≃* alternatingGroup (Fin 6))
  | alternatingSeven (e : L ≃* alternatingGroup (Fin 7))
  | tripleSix (centerEquiv : center L ≃* Multiplicative (ZMod 3))
      (quotientEquiv : (L ⧸ center L) ≃* alternatingGroup (Fin 6))
  | linearFourTwo (e : L ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
  | linearFiveTwo (e : L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))

/-- Inspect all source cases without losing the SL₃ action or dropping an endpoint. -/
theorem linearThree_or_other
    {E : Type u} [Group E] {U : Type v} [AddCommGroup U] [Module (ZMod 2) U]
    (σ : Representation (ZMod 2) E U) {L H : Subgroup E}
    (hc : IrreducibleActionCase σ L H) :
    (∃ F : BinaryField, H = L ∧
      Nonempty (ActionEquiv (σ.comp L.subtype) (linearNatural F 3)) ∧
      quadraticRatio σ = 1 / 2) ∨ OtherModel L := by
  cases hc with
  | linearTwo F _ e _ _ => exact Or.inr (.linearTwo F e.groupEquiv)
  | linearThree F he e hq => exact Or.inl ⟨F, he, ⟨e⟩, hq⟩
  | symplectic F _ _ e _ => exact Or.inr (.symplecticFour F e.groupEquiv)
  | symplecticTwo e _ =>
    exact Or.inr (.alternatingSix (e.subgroupEquiv.trans binarySymplecticDerivedEquiv))
  | g2 F _ _ e _ _ => exact Or.inr (.g2 F e.groupEquiv)
  | g2Two e _ _ => exact Or.inr (.g2DerivedTwo e.subgroupEquiv)
  | symmetric n hn e _ _ =>
    rcases hn with rfl | rfl
    · exact Or.inr (.linearTwo BinaryField.four
        (e.subgroupEquiv.trans alternatingFiveLinearEquiv))
    · exact Or.inr (.alternatingSeven e.subgroupEquiv)
  | alternatingSix _ e _ _ => exact Or.inr (.alternatingSix e.groupEquiv)
  | alternatingSeven _ _ e _ _ _ => exact Or.inr (.alternatingSeven e)
  | tripleSix _ h _ => exact Or.inr (.tripleSix h.centerEquiv h.quotientEquiv)
  | binaryLinear d hd _ e _ =>
    rcases hd with rfl | rfl
    · exact Or.inr (.linearFourTwo e.groupEquiv)
    · exact Or.inr (.linearFiveTwo e.groupEquiv)
  | orthogonalSix _ _ e _ _ =>
    exact Or.inr (.linearFourTwo (e.groupEquiv.trans alternatingEightLinearEquiv))
  | symmetricEight _ e _ =>
    exact Or.inr (.linearFourTwo (e.subgroupEquiv.trans alternatingEightLinearEquiv))
  | exteriorFive _ _ e _ _ _ => exact Or.inr (.linearFiveTwo e)

/-- Apply the complete universal source implication to the actual faithful
irreducible action, obtaining a best offender from its FF hypothesis. -/
theorem fullB42_linearThree_or_other
    {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦)
    {E : Type u} [Group E] [Finite E]
    {U : Type v} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (σ : Representation (ZMod 2) E U) (h : B4Hypotheses 𝒦 σ)
    (hff : IsFFModule σ) :
    (∃ F : BinaryField, offenderSubgroup σ = Theory.GroupTheory.generalizedFitting E ∧
      Nonempty (ActionEquiv (σ.comp (Theory.GroupTheory.generalizedFitting E).subtype)
        (linearNatural F 3)) ∧ quadraticRatio σ = 1 / 2) ∨
      OtherModel (Theory.GroupTheory.generalizedFitting E) := by
  obtain ⟨A, hA⟩ := h.exists_bestOffender hff
  exact linearThree_or_other σ (hB42 E U σ A hA)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo
