module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.M11HigmanSimsSourceHS
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.M11HigmanSimsSourceHSDegreePresentation
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.Saturation
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FixedSpace.OddClasses
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FixedSpace.LargeModels
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.ElevenFixedFree.Universal
public import Theory.Representation.HigmanSims.LargeModels.Binary

/-!
# The original HS degree window reduced to marked presentation faithfulness

The constructed binary twenty-space and four larger binary models, together
with the degree-896 pair and degree-1408 restriction, saturate the proved bound
of nine odd-order conjugacy classes. This gives both the absolute degree window
and universal comparison with the constructed twenty-space. The latter supplies
the order-eleven fixed-space calculation for every absolute twenty-space; power
fusion then forces its traces into the binary field. Thus degree forty is
excluded on the original binary vector space, rather than only after choosing
an algebraic closure.

All representation and center-bound inputs are discharged from their concrete
producers. The one remaining input is faithfulness of the literal ATLAS
presentation map used to descend the degree-896 and degree-1408 matrices. This
module proves conditional source and rank-one applications and does not assert
the unconditional `HigmanSimsDegreeWindow`. Its final discharge remains with
the degree-window task; the independent outer estimates remain with their owner.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
HS paragraph, published p.366 (author-preprint p.16), and Theorem 6.6/Table 6.7;
Aschbacher--Smith K.4, printed p.457/PDF p.468.
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue
open Theory.GroupTheory Subgroup
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech
universe u v

namespace HSDegree
open HigmanSims.AbsoluteWindow.FixedSpace
open Representation.HigmanSims.LargeModels
open _root_.Sporadic.LeechRelated.HS

/-- All seven larger models on the actual carrier, with no matrix, density,
trace or coefficient-extension input remaining. -/
theorem largeModelsExist_of_presentationFaithful
    (hf : Function.Injective AtlasPresentation.toCarrier) : LargeModelsExist.{v} :=
  largeModelsExist_of_finite_models binaryModelsExist
    (traceSeparatedPairExists_of_presentationFaithful hf)
    (restrictedModelExists_of_presentationFaithful hf)

/-- The concrete binary action supplies the small model needed for saturation. -/
theorem twentyModelExists : TwentyModelExists.{v} :=
  twentyModelExists_of_binary_model Twenty.carrierRepresentation
    Twenty.carrierRepresentation_absolutelyIrreducible

/-- Exhaustion of the absolute degree window uses actual simple models and
the proved odd-class bound, not a list of candidate dimensions. -/
theorem absoluteDegreeWindow_of_presentationFaithful
    (hf : Function.Injective AtlasPresentation.toCarrier) :
    HigmanSims.AbsoluteDegreeWindow.{v} :=
  HigmanSims.absoluteDegreeWindow_of_saturating_models oddClassBound
    twentyModelExists (largeModelsExist_of_presentationFaithful hf)

/-- Saturation gives the universal model comparison needed to transfer the
order-eleven calculation. Power fusion then fixes every trace under Frobenius. -/
theorem degreeTwentyTraceField_of_presentationFaithful
    (hf : Function.Injective AtlasPresentation.toCarrier) :
    HigmanSims.DegreeTwentyTraceField.{v} :=
  HigmanSims.degreeTwentyTraceField_of_powerFusion_of_elevenFixedFree
    HigmanSims.TraceField.powerFusion
    (HigmanSims.TraceField.Universal.degreeTwentyElevenFixedFree_of_saturation
      oddClassBound (largeModelsExist_of_presentationFaithful hf))

end HSDegree

/-- Complete representation descent on the original source action, conditional
only on the marked abstract presentation map. In particular no degree-forty,
trace-field, recognition, FF or cubic premise remains. -/
theorem higmanSimsDegreeWindow_of_presentationFaithful
    (hf : Function.Injective _root_.Sporadic.LeechRelated.HS.AtlasPresentation.toCarrier) :
    HigmanSimsDegreeWindow.{u,v} := by
  intro G V _ _ _ _ _ ρ h hd
  let := h.quasisimple
  obtain ⟨e⟩ := h.centralQuotient
  exact h.finrank_eq_twenty_of_representation_inputs
    (Theory.SpecificGroups.J2HSMultipliers.HS.center_isPGroup_of_quotient_equiv e)
    (HSDegree.absoluteDegreeWindow_of_presentationFaithful hf)
    (HSDegree.degreeTwentyTraceField_of_presentationFaithful hf) hd

/-- Apply the original degree window to the literal source-exclusion consumer.
Presentation faithfulness and the independent outer estimates are explicit; all
inner estimates and every representation calculation are discharged. -/
theorem sourceExclusion_hs_of_presentationFaithful_and_outer
    (hf : Function.Injective _root_.Sporadic.LeechRelated.HS.AtlasPresentation.toCarrier)
    (houter : HigmanSimsOuterEstimates.{u,v}) : SourceExclusion.{u,v} .hs :=
  sourceExclusion_hs_of_degree_and_outer
    (higmanSimsDegreeWindow_of_presentationFaithful hf) houter

/-- The same conditional result on the original rank-one source action, using
its literal generalized-Fitting identification and central-quotient marking. -/
theorem not_hs_of_rankOne_source_of_presentationFaithful_and_outer
    (hf : Function.Injective _root_.Sporadic.LeechRelated.HS.AtlasPresentation.toCarrier)
    (houter : HigmanSimsOuterEstimates.{u,v})
    {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
    (h : RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.hs.Carrier)) : False :=
  not_hs_of_rankOne_source_of_degree_and_outer
    (higmanSimsDegreeWindow_of_presentationFaithful hf) houter h he

end CFSG.Quasithin.ChapterK.SporadicCatalogue
