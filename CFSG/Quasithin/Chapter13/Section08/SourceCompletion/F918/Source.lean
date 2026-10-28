module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.F918.Faithful
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.F918.Sections
/-!
# The original source actor on the component-orbit spans

For the literal component orbit K₀ in H=K₀L₁T, the preceding source
Fitting argument supplies quasisimplicity and normality. The genuine
F.9.16 selection constructs one subgroup B in the original edge core.
That same B-star acts faithfully and quadratically on every actual
intermediate orbit span of an Irr⁺ seed. The action images retain both
the quadratic and cubic ratio bounds, so they feed the genuine D.3
module classification without additional actor or section premises.

Use X=K₀-star T-star and X=H-star for the original T- and H-spans.
Sections.seedSpan_join_eq_T_span identifies the former with D.3's literal
orbitSpan. Earlier maximal-local, F.9 applicability,13.5.4 and13.3.9
source inputs remain explicit, as does the preceding reduction H=K₀L₁T.
No D.3 module classification is asserted or assumed here.
Source: Aschbacher--Smith, F.9.18(2--3), printed p.325, applied in
13.8.16, p.952, combined manuscript of1 March2004.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.F918
open CriticalGeometry.Reorientation SolvableExclusion Three Three.Supercritical.Offenders
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree
open Geometry.CoveredProduct.ResidualPlacement
open Components.Swapped.LinearTwo.ModuleAlternatives
open Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections
universe u
variable {G:Type u} [Group G] [Finite G]
 {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}
 (d:LocalSetup T L V V₁ V₂ V₃ M G₁)
 (h:Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
 (hF9all:∀J∈Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
 (hcentral:centralizer (V₃:Set G)≤M⊓normalizer (V:Set G))
 (hcomm:⁅V₃,G₁.pCoreIn 2⁆≠⊥)
 (hsource:Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
 (hH:H∈Source.Hz (one L T V₁) T G₁ M)
 [hEA:IsElementaryAbelian 2 (Source.UH H V₃)]
 (K:Subgroup G) (hKH:K≤H) (hK:(K.subgroupOf H).IsCComponent)
 (hgen:conjugateSpanBy K (T:Subgroup G)⊔(one L T V₁⊔(T:Subgroup G))=H)
include d h hF9all hcentral hcomm hsource hH hKH hK hgen

theorem source_component_span_actors :
    ∃ (a:Five.StarAction H (Source.UH H V₃) V₁) (B:Subgroup G),
      B≤((L⊔(T:Subgroup G))⊓H).pCoreIn 2 ∧ B≤T ∧
      QuadraticMember (linearAction a) (Source.starImage H B) ∧
      Source.starImage H B⊓centralizer (Source.starImage H (conjugateSpanBy K (T:Subgroup G)):Set (Source.Hstar H))=⊥ ∧
      ∀ (I:Submodule (ZMod 2) (Additive (Source.Utilde H V₃ V₁))),
        IsIrrPlus (linearAction a) (Source.starImage H (conjugateSpanBy K (T:Subgroup G))) I →
        ∀ X:Subgroup (Source.Hstar H),Source.starImage H K≤X→Source.starImage H T≤X→
        SpanActorResult (linearAction a) (Source.starImage H B) X I := by
  obtain ⟨a,B,hB,hBT,hq,hfaith⟩:=@source_component_actor G _ _ T L V V₁ V₂ V₃ M G₁ H d hEA h hF9all hcentral hcomm hsource hH K hKH hK hgen
  refine ⟨a,B,hB,hBT,hq,hfaith,?_⟩
  have hTH:(T:Subgroup G)≤H:=le_sup_right.trans hH.1.2
  have ho:=star_conjugateSpan H K T hKH hTH
  have hqs:=(SolvableSource.component_fitting_source d h hF9all hcentral hcomm hsource hH K hK).2
  have hcomp:=star_isComponent H K hK hqs
  rw [ho] at hfaith
  intro I hI X hKX hTX
  rw [ho] at hI
  have haX:Source.starImage H B≤X:=(starImage_mono H hBT).trans hTX
  exact spanActorResult (linearAction a) (Source.starImage H K)
    (Source.starImage H T) (Source.starImage H B) X hcomp hKX hTX haX
    hq.1 hq.2.1 hq.2.2 hfaith I hI

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.F918
