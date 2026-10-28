module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.SourceModels.PairedActor
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.SourceModels.Source
/-!
# The nonnormal F.9.18 model clause on the original quotient

A.3.8 gives the genuine index-two normalizer and its earlier four-family
catalogue on K*. The source component-orbit normality makes relative
nonnormality exactly the moving-orbit case. The same F.9.18 edge actor
acts quadratically on U_H/V1 and faithfully by conjugation on that orbit.
Applying `PairedActor` leaves actual binary PSL2, Suzuki, or PSL3(2)
isomorphisms. The final transport uses the literal equivalence
K/O2(K) ≃ K* required by the Chapter 13 branch eliminations.

Only the original earlier F9, 13.5.4, and 13.3.9 inputs remain explicit.
The branch eliminations and the resulting normality belong to the final
component assembly owner qt-d-138-components-source.

Source: Aschbacher--Smith, F.9.18(5), printed pp.325--326;
original 13.8.16, pp.952--953.
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
  (hn : ¬ (K.subgroupOf H).Normal)

include d h hF9all hcentral hcomm hsource hH hKH hK hgen hn

private theorem source_nonnormal_f918Models_elementary
    [hEA : IsElementaryAbelian 2 (Source.UH H V₃)] :
    NonnormalF918Models (Source.starImage H K) := by
  obtain ⟨a,B,_,hBT,hq,hfaith,_⟩ := F918.source_component_span_actors (hEA := hEA)
    d h hF9all hcentral hcomm hsource hH K hKH hK hgen
  have hf := linearAction_injective a
    (a.injective_of_kernel (OddReduction.source_kernel (hF9all H hH)))
  have hqs := (SolvableSource.component_fitting_source d h hF9all hcentral hcomm hsource hH K hK).2
  have hcomp := star_isComponent H K hK hqs
  obtain ⟨hindex,hmodel⟩ := source_nonnormal_star_models d hH hK hn
  have hmove : ¬ Source.starImage H T ≤ normalizer (Source.starImage H K : Set (Source.Hstar H)) := by
    intro ht
    apply hn
    apply (source_orbit_eq_iff_normal d h hF9all hcentral hcomm hsource hH K hKH hK).mp
    exact le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl ht)
      (le_componentOrbit _ _)
  rw [star_conjugateSpan H K T hKH (le_sup_right.trans hH.1.2),
    conjugateSpanBy_eq_iSup_conj] at hfaith
  exact nonnormal_models_of_quadratic_actor (linearAction a) (Source.starImage H K)
    (Source.starImage H T) (Source.starImage H B) hcomp (CoverModels.original_star_sqtk d hH)
    hmodel hindex hmove hf (starImage_mono H hBT) hq.1 hq.2.1 hq.2.2 hfaith

theorem source_nonnormal_f918Models : NonnormalF918Models (Source.starImage H K) := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hH
  exact source_nonnormal_f918Models_elementary d h hF9all hcentral hcomm hsource hH hKH hK hgen hn

/-- F.9.18(5) on the component's intrinsic two-core quotient. -/
theorem source_nonnormal_quotient_f918Models : NonnormalF918Models (K ⧸ pCore 2 K) :=
  (source_nonnormal_f918Models d h hF9all hcentral hcomm hsource hH hKH hK hgen hn).transport
    (componentStarEquiv H K hKH hK)

end Original
end CFSG.Quasithin.Chapter13.Section08.Components.SourceModels
