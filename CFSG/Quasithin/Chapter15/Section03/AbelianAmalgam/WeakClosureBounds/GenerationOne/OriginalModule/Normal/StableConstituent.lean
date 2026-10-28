module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio.Table
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource.EvenRankOne
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceQuadratic
public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.Symplectic
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.ActionHypotheses

/-!
# Natural constituents on the original stable component section

The actual even-family source classifiers give the B.4 action alternatives on
this representation. Comparing the marked simple central quotient at odd field
exponent greater than one leaves the natural SL₂, Suzuki, SL₃ and Sp₄ actions,
with their original intertwiners and exact defining-field cardinalities. The
corrected projective-line B.4.2 output is inspected directly.

For a normal centerless quasisimple component, the literal central-section
map embeds the component as the whole generalized Fitting subgroup of the
faithful image. This transports the source marking and pulls the recognized
action back to the original component, retaining the map needed for its Borel.

Source: Aschbacher–Smith, B.4.2–5, pp.86–87; F.9.18(3–4), pp.325–326;
and the constituent deduction in 15.3.65, p.1152.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Matrix
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal
open RepresentationReduction.SourceRestrictions.Cases
open Single.SmallRatio RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity

private def consumerField (F : ChapterB.QuasisimpleSource.BinaryField) : BinaryField where
  Carrier := F.Carrier
  degree := F.degree
  degree_pos := F.degree_pos
  card_eq := F.card_eq

universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) {L H : Subgroup D} {f : ℕ}

theorem natural_of_projective_B42 (hs : SourceModel (L ⧸ center L) f)
    (hf : 1 < f) (ho : Odd f) (hz : center L = ⊥)
    (h : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L H) : NaturalConstituent ρ L f := by
  cases h with
  | linearTwo F _ e _ _ =>
    have hc := hs.componentModel hf ho (.linearTwo F.Carrier F.degree_pos F.card_eq
      (centralQuotientCongr e.groupEquiv))
    exact .linearTwo (consumerField F) (F.card_eq.trans hc.2)
      ⟨e.groupEquiv, e.linearEquiv, e.intertwines⟩
  | linearThree F _ e _ =>
    have hc := hs.componentModel hf ho (.linearThree F.Carrier F.degree_pos F.card_eq
      (centralQuotientCongr e.groupEquiv))
    exact .linearThree (consumerField F) (F.card_eq.trans hc.2)
      ⟨e.groupEquiv, e.linearEquiv, e.intertwines⟩
  | symplectic F hn _ e _ =>
    have hc := hs.componentModel hf ho (.symplecticFour F.Carrier hn F.card_eq
      (centralQuotientCongr e.groupEquiv))
    exact .symplecticFour (consumerField F) (F.card_eq.trans hc.2)
      ⟨e.groupEquiv, e.linearEquiv, e.intertwines⟩
  | symplecticTwo e _ =>
    have hc := hs.componentModel hf ho (.symplecticFourTwoDerived
      ((centerQuotientEquiv hz).trans e.subgroupEquiv))
    rcases hc.1 with he | he | he <;> cases he
  | g2 F hn _ e _ _ =>
    have hc := hs.componentModel hf ho (.gTwo F.Carrier hn F.card_eq
      ((centerQuotientEquiv hz).trans e.groupEquiv))
    rcases hc.1 with he | he | he <;> cases he
  | g2Two e _ _ =>
    have hc := hs.componentModel hf ho (.gTwoTwoDerived
      ((centerQuotientEquiv hz).trans e.subgroupEquiv))
    rcases hc.1 with he | he | he <;> cases he
  | symmetric n hn e _ _ =>
    rcases hn with rfl | rfl
    · have hc := hs.componentModel hf ho (.alternatingFive
        ((centerQuotientEquiv hz).trans e.subgroupEquiv))
      rcases hc.1 with he | he | he <;> cases he
    · have hc := hs.componentModel hf ho (.alternatingSeven
        ((centerQuotientEquiv hz).trans e.subgroupEquiv))
      rcases hc.1 with he | he | he <;> cases he
  | alternatingSix _ e _ _ =>
    have hc := hs.componentModel hf ho (.alternatingSix
      ((centerQuotientEquiv hz).trans e.groupEquiv))
    rcases hc.1 with he | he | he <;> cases he
  | alternatingSeven _ _ e _ _ _ =>
    have hc := hs.componentModel hf ho (.alternatingSeven
      ((centerQuotientEquiv hz).trans e))
    rcases hc.1 with he | he | he <;> cases he
  | tripleSix _ a _ =>
    have hc := hs.componentModel hf ho (.alternatingSix a.quotientEquiv)
    rcases hc.1 with he | he | he <;> cases he
  | binaryLinear d hd _ e _ =>
    rcases hd with rfl | rfl
    · have hc := hs.componentModel hf ho (.linearFourTwo (centralQuotientCongr e.groupEquiv))
      rcases hc.1 with he | he | he <;> cases he
    · have hc := hs.componentModel hf ho (.linearFiveTwo (centralQuotientCongr e.groupEquiv))
      rcases hc.1 with he | he | he <;> cases he
  | orthogonalSix _ _ e _ _ =>
    have hc := hs.componentModel hf ho (.linearFourTwo
      (centralQuotientCongr (e.groupEquiv.trans alternatingEightLinearEquiv)))
    rcases hc.1 with he | he | he <;> cases he
  | symmetricEight _ e _ =>
    have hc := hs.componentModel hf ho (.linearFourTwo
      (centralQuotientCongr (e.subgroupEquiv.trans alternatingEightLinearEquiv)))
    rcases hc.1 with he | he | he <;> cases he
  | exteriorFive _ _ e _ _ _ =>
    have hc := hs.componentModel hf ho (.linearFiveTwo (centralQuotientCongr e))
    rcases hc.1 with he | he | he <;> cases he


variable [Finite D] [FiniteDimensional (ZMod 2) V]

/-- Each marked even model is classified on the original action. -/
theorem actionCase_or_table_of_sourceModel
    (hyp : ChapterK.RankOne.SourceHypotheses ρ L) (hq : quadraticRatio ρ ≤ 2)
    (hs : SourceModel (L ⧸ center L) f) (hf : 1 < f) :
    ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase
      ρ L (offenderSubgroup ρ) ∨
    Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource.TableB45 ρ L := by
  cases hs with
  | linearTwo F hF e =>
    exact ChapterB.SmallRatioClassification.psl2_case hyp (r := f) (by omega)
      ⟨F, inferInstance, inferInstance, hF, ⟨e⟩⟩
  | suzuki m hm he e =>
    exact Or.inr (ChapterB.SmallRatioClassification.suzuki_table hyp (by omega) e)
  | unitary F J hF hc e =>
    exact Or.inr (ChapterB.SmallRatioClassification.unitary_table hyp (n := f) (by omega)
      ⟨F, inferInstance, inferInstance, J, hF, hc, ⟨e⟩⟩)
  | linearThree F hF e =>
    exact Or.inl (ChapterK.Linear.Recognition.SourceQuadratic.actionCase_of_quadratic_le_two
      ⟨inferInstance, inferInstance, hyp.sqtk, hyp.fitting, hyp.quasisimple,
        hyp.faithful, hyp.irreducible, hyp.smallCubic⟩
      f (by omega) ⟨F, inferInstance, inferInstance, hF, ⟨e⟩⟩ hq)
  | symplecticFour F hF e =>
    exact Or.inl (ChapterB.SmallRatioClassification.symplectic_model_case hyp hq (r := f) (by omega)
      ⟨F, inferInstance, inferInstance, hF, ⟨e.trans (symplecticProjectiveEquiv hf hF)⟩⟩)

/-- The actual source classifiers recognize the natural constituent and its field. -/
theorem natural_of_sourceModel
    (hyp : ChapterK.RankOne.SourceHypotheses ρ L) (hq : quadraticRatio ρ ≤ 2)
    (hs : SourceModel (L ⧸ center L) f) (hf : 1 < f) (ho : Odd f)
    (hz : center L = ⊥) : NaturalConstituent ρ L f := by
  rcases actionCase_or_table_of_sourceModel ρ hyp hq hs hf with h | h
  · exact natural_of_projective_B42 ρ hs hf ho hz h
  · exact natural_of_table_B45 ρ hs hf ho hz hq h

/-- Apply the source classification to the whole generalized Fitting subgroup. -/
theorem natural_of_B4_source [Finite V]
    (hyp : B4Hypotheses KnownSimple.IsKnownSimple ρ) (hq : quadraticRatio ρ ≤ 2)
    (hs : SourceModel (generalizedFitting D ⧸ center (generalizedFitting D)) f)
    (hf : 1 < f) (ho : Odd f) (hz : center (generalizedFitting D) = ⊥) :
    NaturalConstituent ρ (generalizedFitting D) f :=
  natural_of_sourceModel ρ
    ⟨hyp.sqtk, rfl, hyp.quasisimple, hyp.faithful, hyp.irreducible,
      (Representation.BinaryOffender.cubicRatio_le_quadraticRatio ρ).trans hq⟩
    hq hs hf ho hz


section SectionConsumer
variable {D V : Type u} [Group D] [Finite D] [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [K.Normal]
    [IsQuasisimple K] (I : Subrepresentation ρ) {f : ℕ}
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage.Structure

/-- Centerlessness passes to the exact generalized Fitting subgroup of the section image. -/
theorem section_fitting_centerless (hi : IsIrrPlus ρ K I.toSubmodule)
    (hquot : IsPGroup 2 (D ⧸ K)) (hZ : center K = ⊥) :
    center (generalizedFitting (actionImage (Single.sectionRepresentation ρ K I))) = ⊥ := by
  let σ := Single.sectionRepresentation ρ K I
  have hsurvive := Single.section_component_survives ρ K I hi
  have hfit := (image_structure σ K hsurvive hquot
    (Single.section_component_irreducible ρ K I hi)).2.2
  rw [hfit]
  exact centerless_of_equiv hZ (componentEquiv σ K hsurvive hZ)

/-- The genuine classifiers apply to the literal central section, with no B.4 callback. -/
theorem section_natural_of_image_model
    (hi : IsIrrPlus ρ K I.toSubmodule) (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (hquot : IsPGroup 2 (D ⧸ K)) (hZ : center K = ⊥)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A) (hAC : A ⊓ centralizer (K : Set D) = ⊥)
    (hm : SourceModel
      (generalizedFitting (actionImage (Single.sectionRepresentation ρ K I)) ⧸
        center (generalizedFitting (actionImage (Single.sectionRepresentation ρ K I)))) f)
    (hf : 1 < f) (ho : Odd f) :
    NaturalConstituent (imageRepresentation (Single.sectionRepresentation ρ K I))
      (generalizedFitting (actionImage (Single.sectionRepresentation ρ K I))) f :=
  natural_of_B4_source (imageRepresentation (Single.sectionRepresentation ρ K I))
    (Single.section_B4_hypotheses ρ K I hi hs hquot hZ)
    (Single.section_quadratic_bound ρ K I hi A hA hq hc hAC)
    hm hf ho (section_fitting_centerless ρ K I hi hquot hZ)

/-- The original component marking transports through its actual faithful section map. -/
theorem section_natural_of_sourceModel
    (hi : IsIrrPlus ρ K I.toSubmodule) (hs : IsSQTK KnownSimple.IsKnownSimple D)
    (hquot : IsPGroup 2 (D ⧸ K)) (hZ : center K = ⊥)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A) (hAC : A ⊓ centralizer (K : Set D) = ⊥)
    (hm : SourceModel (K ⧸ center K) f) (hf : 1 < f) (ho : Odd f) :
    NaturalConstituent (imageRepresentation (Single.sectionRepresentation ρ K I))
      (generalizedFitting (actionImage (Single.sectionRepresentation ρ K I))) f := by
  let σ := Single.sectionRepresentation ρ K I
  have hsurvive := Single.section_component_survives ρ K I hi
  have hfit := (image_structure σ K hsurvive hquot
    (Single.section_component_irreducible ρ K I hi)).2.2
  let e : K ≃* generalizedFitting (actionImage σ) :=
    (componentEquiv σ K hsurvive hZ).trans (MulEquiv.subgroupCongr hfit.symm)
  exact section_natural_of_image_model ρ K I hi hs hquot hZ A hA hq hc hAC
    (hm.transport (centralQuotientCongr e).symm) hf ho

/-- The component map identifies K with the whole F* of the faithful section image. -/
@[expose] def sectionComponentEquiv (hi : IsIrrPlus ρ K I.toSubmodule)
    (hquot : IsPGroup 2 (D ⧸ K)) (hZ : center K = ⊥) :
    K ≃* generalizedFitting (actionImage (Single.sectionRepresentation ρ K I)) := by
  let σ := Single.sectionRepresentation ρ K I
  have hsurvive := Single.section_component_survives ρ K I hi
  have hfit := (image_structure σ K hsurvive hquot
    (Single.section_component_irreducible ρ K I hi)).2.2
  exact (componentEquiv σ K hsurvive hZ).trans (MulEquiv.subgroupCongr hfit.symm)

/-- Pull back a recognized image action through the original component's actual map.
The resulting actor isomorphism is the one to use when transporting its Borel. -/
@[expose] def sectionIdentification
    {E X : Type*} [Group E] [AddCommGroup X] [Module (ZMod 2) X]
    {τ : Representation (ZMod 2) E X}
    (hi : IsIrrPlus ρ K I.toSubmodule)
    (hquot : IsPGroup 2 (D ⧸ K)) (hZ : center K = ⊥)
    (a : ActionEquiv
      ((imageRepresentation (Single.sectionRepresentation ρ K I)).comp
        (generalizedFitting (actionImage (Single.sectionRepresentation ρ K I))).subtype) τ) :
    RepresentationReduction.SourceRestrictions.CentralQuotientIdentification
      ρ K I.toSubmodule hi.choose τ where
  groupEquiv := (sectionComponentEquiv ρ K I hi hquot hZ).trans a.groupEquiv
  linearEquiv := a.linearEquiv
  equivariant k v := by
    rw [← Single.sectionRepresentation_component ρ K I hi.choose k v]
    exact a.intertwines (sectionComponentEquiv ρ K I hi hquot hZ k) v

end SectionConsumer


end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal
