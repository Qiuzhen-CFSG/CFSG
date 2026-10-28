module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.F918.Actors
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Solvable.Original
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Offenders.PrimeCoreAction
/-!
# Faithfulness of the original edge actor on the component supplement

The intersection of the edge two-core image with the centralizer of a
normal supplement is a normal two-subgroup of H/O₂(H), hence trivial.
The actor constructed in F.9.16 therefore acts faithfully on that actual
supplement. Its placement in T follows from Sylow maximality.

For the original component orbit, the preceding source residual and
solvable-exclusion arguments prove its normality. The final consumer
retains only those genuine earlier source hypotheses and H=K₀L₁T;
no core-faithfulness or actor-choice conclusion is an input.
Source: Aschbacher--Smith, F.9.18(2), p.325, and13.8.15--16, p.952.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.F918
open CriticalGeometry CriticalGeometry.Reorientation SolvableExclusion Three Three.Supercritical.Offenders
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree
open Geometry.CoveredProduct.ResidualPlacement
variable {G:Type*} [Group G] [Finite G]

private theorem edge_core_faithful (H P J:Subgroup G)
    (hgen:P⊔J=H) (hn:H≤normalizer (P:Set G)) :
    Source.starImage H (J.pCoreIn 2)⊓centralizer (Source.starImage H P:Set (Source.Hstar H))=⊥ := by
  have hp:P≤H:=hgen ▸ le_sup_left
  have hj:J≤H:=hgen ▸ le_sup_right
  let : (P.subgroupOf H).Normal:=(normal_subgroupOf_iff_le_normalizer hp).mpr hn
  let : (Source.starImage H P).Normal:=(inferInstance : (P.subgroupOf H).Normal).map (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective (pCore 2 H))
  have hgen':Source.starImage H P⊔Source.starImage H J=⊤ := by
    unfold Source.starImage
    rw [←Subgroup.map_sup,←subgroupOf_sup hp hj,hgen,subgroupOf_self,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  exact centralizer_inf_eq_bot_of_supplement _ _ _ hgen'
    (starImage_isPGroup H _ (isPGroup_pCoreIn 2 J))
    (starImage_normalizes H (le_normalizer_pCoreIn 2 J)) (hstar_twoCore H)

variable {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}
 (d:LocalSetup T L V V₁ V₂ V₃ M G₁)
 (hF9:(Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
 [IsElementaryAbelian 2 (Source.UH H V₃)]
include d hF9

theorem exists_faithful_edge_actor (P:Subgroup G)
    (hgen:P⊔((L⊔(T:Subgroup G))⊓H)=H) (hn:H≤normalizer (P:Set G)) :
    ∃ (a:Five.StarAction H (Source.UH H V₃) V₁) (B:Subgroup G),
      B≤((L⊔(T:Subgroup G))⊓H).pCoreIn 2 ∧ B≤T ∧
      QuadraticMember (linearAction a) (Source.starImage H B) ∧
      Source.starImage H B⊓centralizer (Source.starImage H P:Set (Source.Hstar H))=⊥ := by
  obtain ⟨a,B,hB,hq⟩:=exists_edge_quadratic_actor d hF9
  have hT:(T:Subgroup G)≤(L⊔(T:Subgroup G))⊓H:=le_inf le_sup_right hF9.T_le_H
  have hcoreT:((L⊔(T:Subgroup G))⊓H).pCoreIn 2≤T :=
    (isPGroup_pCoreIn 2 _).le_sylow_of_normalized T (hT.trans (le_normalizer_pCoreIn 2 _))
  refine ⟨a,B,hB,hB.trans hcoreT,hq,?_⟩
  apply bot_unique
  exact (inf_le_inf_right _ (starImage_mono H hB)).trans_eq (edge_core_faithful H P _ hgen hn)

variable (h:Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
 (hF9all:∀J∈Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
 (hcentral:centralizer (V₃:Set G)≤M⊓normalizer (V:Set G))
 (hcomm:⁅V₃,G₁.pCoreIn 2⁆≠⊥)
 (hsource:Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
include h hF9all hcentral hcomm hsource
omit hF9 in
theorem source_component_actor (hH:H∈Source.Hz (one L T V₁) T G₁ M)
    (K:Subgroup G) (hKH:K≤H) (hK:(K.subgroupOf H).IsCComponent)
    (hgen:conjugateSpanBy K (T:Subgroup G)⊔(one L T V₁⊔(T:Subgroup G))=H) :
    ∃ (a:Five.StarAction H (Source.UH H V₃) V₁) (B:Subgroup G),
      B≤((L⊔(T:Subgroup G))⊓H).pCoreIn 2 ∧ B≤T ∧
      QuadraticMember (linearAction a) (Source.starImage H B) ∧
      Source.starImage H B⊓centralizer (Source.starImage H (conjugateSpanBy K (T:Subgroup G)):Set (Source.Hstar H))=⊥ := by
  have hex:=SolvableSource.solvable_overgroup_source d h hF9all hcentral hcomm hsource
  have hn:=(LocalFitting.source_component d hH hsource hex K hKH hK).2.2.1
  apply exists_faithful_edge_actor d (hF9all H hH) _ _ hn
  rwa [Comparison.local_edge d (hF9all H hH)]

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.F918
