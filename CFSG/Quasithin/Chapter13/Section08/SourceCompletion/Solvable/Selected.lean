module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Solvable.NoTransvections
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Comparison.Geometry
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five

/-!
# Actual quadratic selection in a solvable source overgroup

The literal action of H/O₂(H) on UH/V₁ is faithful by the F.9 kernel
identity. The solvable transvection exclusion makes both critical
commutator-preimage denominators proper. The source common-center bound
then selects the actual orientation with a quadratic actor. Incidence
constructs its conjugate placement in the original parabolic core.

The output retains one action and one critical pair; every geometric field
used by the three-primary reduction is proved for that pair. Only the
earlier F.9, flag-normalizer and original commutator statements remain.
Source: Aschbacher--Smith, 13.8.8 and 13.8.13, printed pp.949--951.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.SolvableSource
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree
open Geometry.CoveredProduct.ResidualPlacement
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open CriticalGeometry CriticalGeometry.Reorientation
open SolvableExclusion Three.Supercritical.Offenders
open Five.Localization.EndpointGeometry
variable {G:Type*} [Group G] [Finite G]
 {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}
 (d:LocalSetup T L V V₁ V₂ V₃ M G₁)
 (hH:H∈Source.Hz (one L T V₁) T G₁ M)
 (hF9:(Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
 (hN:Nonempty ((L⧸pCore 2 L)≃*Atlas.Codes.HexEvenAutomorphisms)→normalizer (zero L:Set G)≤M)
 (hflag:normalizer (V₁:Set G)⊓normalizer (V₃:Set G)≤M⊓normalizer (V:Set G))
 (hdisp:V₁=⁅V₃,Source.QH H⁆)
 (hnoncentral:¬⁅Source.VH H V,H⁆≤Source.UH H V₃)
 [IsElementaryAbelian 2 (Source.UH H V₃)]
include d hH hF9 hN hflag hdisp hnoncentral

theorem exists_selected (hs:Group.IsSolvable H) :
    ∃ (a:Five.StarAction H (Source.UH H V₃) V₁)
      (c:CriticalPair L T H V),
      Three.RankOne.Geometry c V₃ V₁ (one L T V₁) ∧
      denominatorRank V₃ V₁ c≤rank (Source.starImage H (c.Ugamma V₃)) ∧
      QuadraticMember (linearAction a) (Source.starImage H (c.Ugamma V₃)) := by
  let : IsElementaryAbelian 2 V:=hF9.elementary
  let dn:=localNaturalSetup d
  let : IsElementaryAbelian 2 (conjugateSpanBy V G₁):=d.span_elementary
  let : IsElementaryAbelian 2 (Source.VH H V):=
    IsElementaryAbelian.of_le (conjugateSpanBy_mono le_rfl hH.2.1)
  have hz:H≤normalizer (V₁:Set G):=hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  have hQ:⁅Source.UH H V₃,Source.QH H⁆≤V₁:=hF9.commutator_UH_QH_le_point
  have hgeo:=local_earlierGeometry d hF9
  obtain ⟨a,ha⟩:=Five.exists_faithful_source_starAction H V₃ V₁ hz (OddReduction.source_kernel hF9)
  let act:SourceAction H V₃ V₁ := {
    line_le:=d.line_le_uh H
    seed_le:=hF9.plus_le_H
    representation:=linearAction a
    conjugation:=a.conjugation }
  let sec:=Comparison.sourceSection act hF9.H_centralizes
  have hcentral:⁅Source.VH H V,Source.HC H V₃⁆≤V₁ := by
    rw [commutator_comm]
    exact Section07.centralizer_UH_commutator dn hF9
  have h135:Five.TransvectionComponentConclusion a T := by
    intro t hn ht
    exact (no_star_transvection d hH hF9 hN hflag hdisp hs a t hn ht).elim
  obtain ⟨c,_,_⟩:=dn.exists_criticalPair d.abelian_span hF9
  have hbad:=f9_commutator_not_le_Aone _ hF9 c (hgeo c).length
  obtain ⟨hDH,hDg⟩:=c.strict_denominators_of_no_uStar_transvection V₃ V₁ d.seed_le hz hQ
    (hgeo c) d.line_card hcentral hbad (no_uStar_transvection a hz hQ hs h135)
  obtain ⟨c,hDH,hDg,hpos,hcomp,hquad⟩:=dn.exists_quadratic_selection d.abelian_span hF9 sec c hDH hDg
  have he:=Comparison.local_edge d hF9
  have hcore:= (f9_endpoint_edge_cores _ hF9 c (hgeo c).length).2
  obtain ⟨h,_,hplace,_⟩:=exists_second_to_base c (one L T V₁)
    ((one L T V₁⊔(T:Subgroup G)).pCoreIn 2) (by have:= (hgeo c).length; omega) he hcore le_rfl
  have hU:Source.UH H V₃≤(edgeGroup L T H c.gamma c.previous).pCoreIn 2 := by
    have hh:=(f9_endpoint_edge_cores _ hF9 c (hgeo c).length).1
    change Source.VH H V≤(vertexGroup _ _ _ c.previous⊓vertexGroup _ _ _ c.gamma).pCoreIn 2 at hh
    rw [inf_comm] at hh
    exact (conjugateSpanBy_mono d.seed_le le_rfl).trans hh
  refine ⟨a,c,?_,hcomp,hquad⟩
  exact {
    seed_le:=d.seed_le
    V_le:=hF9.V_le_H
    line_le:=d.line_le_uh H
    line_normalized:=hz
    line_card:=d.line_card
    Vgamma_le:=(hgeo c).Vgamma_H
    placement:=⟨h,hplace⟩
    base_edge:=he
    endpoint_core:=hU
    DH_kernel:=(hgeo c).DH_kernel
    Dgamma_kernel:=(hgeo c).Dgamma_kernel
    DH_strict:=hDH
    Dgamma_strict:=hDg
    comparison:=c.index_comparison_of_selected_rank V₃ V₁
      ((map_mono (conjugateSpanBy_mono d.seed_le le_rfl)).trans (hgeo c).Vgamma_H)
      (hgeo c).Dgamma_kernel hcomp
    core_commutator:=hQ
    noncentral:=hnoncentral
    edge_commutator:=c.edge_commutator_le_of_flag V₃ d.seed_le
      (Comparison.local_seed_index d) hnoncentral (inf_le_left.trans d.normalizes_V) }

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.SolvableSource
