module

public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.UnmarkedQuadratic.Complete
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.SourceModels.Classification

/-!
# The complete small-quadratic model consequence on the original component

The proved FF classification and the completed unmarked non-FF sieve give
the F.9.18 models, including the genuine Mathieu triple cover and the
exclusion of 3.A7. All ten residual families have been excluded on the
original action, with no displacement marking or classification callback.

An actual isomorphism from the source star image transports the models into
`CoverModels.original_catalogue_or_suzuki`, retaining its original local
hypotheses. Constructing the source action and this isomorphism remains with
the F.9.18 owner. The earlier partial-reduction APIs remain available.

Source: Aschbacher--Smith B.4.5, printed p.87, Chapter K, pp.451--460,
F.9.18(4), pp.325--326, and 13.8.17, p.953.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.Components.SourceModels
open Models
open ChapterB.SmallRatioClassification.UnmarkedQuadratic
open Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
universe u v w
variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  (ρ : Representation (ZMod 2) D V)

/-- Only a non-FF action in an explicitly marked outstanding family can
remain after the unmarked quadratic source reduction. -/
theorem f918Models_or_nonFF_remaining
    (hyp : B4Hypotheses KnownSimple.IsKnownSimple ρ) (hq : quadraticRatio ρ ≤ 2) :
    F918Models (generalizedFitting D) ∨
      (¬ IsFFModule ρ ∧ RemainingModel (generalizedFitting D)) := by
  by_cases hff : IsFFModule ρ
  · exact Or.inl (f918Models_of_ff ρ hyp hff)
  · exact (b4_models_or_remaining hyp hq).imp id (fun h => ⟨hff, h⟩)

/-- B.4.2 and the completed non-FF classification give the exact F.9.18
model clause from the B.4 hypotheses and quadratic bound alone. -/
theorem f918Models_of_small_quadratic
    (hyp : B4Hypotheses KnownSimple.IsKnownSimple ρ) (hq : quadraticRatio ρ ≤ 2) :
    F918Models (generalizedFitting D) := by
  by_cases hff : IsFFModule ρ
  · exact f918Models_of_ff ρ hyp hff
  · exact b4_models_of_nonFF hyp hq hff

section Original
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type w} [Group G] [Finite G]
  {T : Sylow 2 G} {L₀ V₀ V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L₀ V₀ V₁ V₂ V₃ M G₁)
  (hH : H ∈ Source.Hz (one L₀ T V₁) T G₁ M)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L₀)
  (hF9all : ∀ J ∈ Source.Hz (one L₀ T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L₀ V₀ V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V₀ : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : SolvableExclusion.Residual.Source1339
    L₀ (one L₀ T V₁) (plus L₀ T V₁) T M V₀ V₁)
  (hK : (K.subgroupOf H).IsCComponent)

include d hH h hF9all hcentral hcomm hsource hK

/-- Apply every completed small-quadratic branch to the literal cover
consumer. The remaining disjunct is still an obligation, not a source theorem. -/
theorem source_catalogue_or_nonFF_remaining
    (hyp : B4Hypotheses KnownSimple.IsKnownSimple ρ) (hq : quadraticRatio ρ ≤ 2)
    (e : Source.starImage H K ≃* generalizedFitting D) :
    ComponentModelOrSuzuki (Source.starImage H K) ∨
      (¬ IsFFModule ρ ∧ RemainingModel (generalizedFitting D)) := by
  rcases f918Models_or_nonFF_remaining ρ hyp hq with hm | hr
  · exact Or.inl (CoverModels.original_catalogue_or_suzuki
      d hH h hF9all hcentral hcomm hsource hK (f918Models_transport e hm))
  · exact Or.inr hr

/-- The actual small-quadratic source action discharges the F.9.18 model
premise of the original cover consumer through its literal star-image
isomorphism. Every original local-source premise is retained. -/
theorem source_catalogue_of_small_quadratic
    (hyp : B4Hypotheses KnownSimple.IsKnownSimple ρ) (hq : quadraticRatio ρ ≤ 2)
    (e : Source.starImage H K ≃* generalizedFitting D) :
    ComponentModelOrSuzuki (Source.starImage H K) := by
  exact CoverModels.original_catalogue_or_suzuki
    d hH h hF9all hcentral hcomm hsource hK
    (f918Models_transport e (f918Models_of_small_quadratic ρ hyp hq))

end Original
end CFSG.Quasithin.Chapter13.Section08.Components.SourceModels
