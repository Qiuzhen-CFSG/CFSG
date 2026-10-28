module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.SourceModels.QuadraticActor
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.SourceModels.Source
/-!
# The normal F.9.18 model clause on the original quotient

F.9.18's actual edge actor is faithful and quadratic on U_H/V1 and acts
faithfully by conjugation on K*. Relative normality identifies its component
orbit with K*. The genuine A.3.6 result bounds the center by order one or
three, so `QuadraticActor` gives all F.9.18(4) group models, including the
central quotient, Mathieu alternatives, and the exclusion of the A7 triple
cover. The final theorem applies this result to the concrete cover consumer.

Only the original earlier F9, 13.5.4, and 13.3.9 inputs remain explicit.
Relative normality is deliberately retained for the assembly owner
qt-d-138-components-source, which also owns the Suzuki exclusion.

Source: Aschbacher--Smith, F.9.18(4), printed pp.325--326;
original 13.8.16--17, pp.952--953.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.Components.SourceModels
open Models
universe u
section Original
open CriticalGeometry.Reorientation
open SourceCompletion SolvableExclusion Three Three.Supercritical.Offenders
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Swapped.LinearTwo.ModuleAlternatives.F918Sections
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V₀ V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V₀ V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V₀ V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V₀ : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V₀ V₁)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G)) = H)
  (hn : (K.subgroupOf H).Normal)

include d h hF9all hcentral hcomm hsource hH hKH hK hgen hn

private theorem source_normal_f918Models_elementary
    [hEA : IsElementaryAbelian 2 (Source.UH H V₃)] : Models.F918Models (Source.starImage H K) := by
  obtain ⟨a,B,_,_,hq,hfaith,_⟩ := F918.source_component_span_actors (hEA := hEA)
    d h hF9all hcentral hcomm hsource hH K hKH hK hgen
  have hf := linearAction_injective a
    (a.injective_of_kernel (OddReduction.source_kernel (hF9all H hH)))
  let : IsQuasisimple (Source.starImage H K) :=
    (SolvableSource.component_fitting_source d h hF9all hcentral hcomm hsource hH K hK).2
  let : (Source.starImage H K).Normal :=
    hn.map _ (QuotientGroup.mk'_surjective (pCore 2 H))
  have hsq := CoverModels.original_star_sqtk d hH
  have hcenter : Nat.card (center (Source.starImage H K)) = 1 ∨
      Nat.card (center (Source.starImage H K)) = 3 := by
    rcases ChapterA.Section03.SourceEmbeddings.quasisimple_containing_component_models_knownSimple
      hsq (pCore_quotient_pCore_eq_bot 2) (starImage_isCComponent H K hK) with
      ⟨hs,_⟩ | ⟨⟨e⟩,_⟩
    · let := hs
      exact Or.inl (Subgroup.card_eq_one.mpr CoverModels.center_eq_bot_of_simple)
    · exact Or.inr ((Nat.card_congr e.toEquiv).trans (Nat.card_zmod 3))
  rw [conjugateSpan_eq_of_normal H K T hKH (le_sup_right.trans hH.1.2) hn] at hfaith
  exact f918Models_of_quadratic_actor (linearAction a) (Source.starImage H K)
    (Source.starImage H B) hf hcenter hsq hq.1 hq.2.1 hq.2.2 hfaith

theorem source_normal_f918Models : Models.F918Models (Source.starImage H K) := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hH
  exact source_normal_f918Models_elementary d h hF9all hcentral hcomm hsource hH hKH hK hgen hn

theorem source_normal_catalogue_or_suzuki : ComponentModelOrSuzuki (Source.starImage H K) :=
  CoverModels.original_catalogue_or_suzuki d hH h hF9all hcentral hcomm hsource hK
    (source_normal_f918Models d h hF9all hcentral hcomm hsource hH hKH hK hgen hn)

end Original
end CFSG.Quasithin.Chapter13.Section08.Components.SourceModels
