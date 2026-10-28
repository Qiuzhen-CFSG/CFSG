module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Comparison.Geometry
public import CFSG.Quasithin.Chapter13.Section07.Preliminaries
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.EndpointGeometry.SourceActions
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Offenders.ModuleAction
public import Theory.Representation.BinaryOffender.InvolutionRatio
public import Theory.Representation.OrthogonalFourMinusRankOne.InnerClassification.Conjugacy
/-!
# A quadratic actor in the original edge core

This proves the actual F.9.16(3) actor in the A6 source configuration.
When both critical denominators are proper, genuine reversal and the
common-center rank bound select an endpoint actor; incidence puts its
conjugate in the original edge core. In either full-denominator case a
nonidentity transvection supplies a cyclic involution actor. The chosen
endpoint transporter carries the terminal edge itself to the base edge,
so the returned transvection already lies in its two-core.

No solvability, absence of transvections, selected geometry or module
classification is assumed. The original abelian span and genuine F.9
applicability are retained. This supplies the actor required by F.9.18(2).
Source: Aschbacher--Smith, F.9.16(1--4), printed pp.323--324, and
F.9.18(2), p.325, applied in13.8.16.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.F918
open CriticalGeometry CriticalGeometry.Reorientation CriticalGeometry.AsymmetricPair
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree
open Geometry.CoveredProduct.ResidualPlacement
open SolvableExclusion Three.Supercritical.Offenders
open Five.Localization.EndpointGeometry
variable {G:Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem quadraticMember_conj {E:Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] {H:Subgroup G}
    (ρ:Representation (ZMod 2) (Source.Hstar H) E) {P:Subgroup G}
    (hP:P≤H) (hQ:QuadraticMember ρ (Source.starImage H P)) (h:H) :
    QuadraticMember ρ (Source.starImage H (P.conjBy (h:G))) := by
  change QuadraticMember ρ (Source.starImage H (P.map (MulAut.conj (h:G)).toMonoidHom))
  rw [MarkedGeometry.starImage_conjugate P hP h]
  refine ⟨hQ.1.map_conj _,?_,?_⟩
  · exact (Representation.OrthogonalFourMinus.RankOne.InnerTransport.quadratic_conj_iff ρ _ _).mpr hQ.2.1
  · simpa only [fixedCodim_map_conj,rank_map_conj] using hQ.2.2

private theorem transvection_actor {H U Z P:Subgroup G}
    [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 P]
    (a:Five.StarAction H U Z) (ht:TransvectionGroup (centerAction a) P) :
    ∃B:Subgroup G,B≤P ∧ QuadraticMember (linearAction a) (Source.starImage H B) := by
  obtain ⟨t,htP,hn,ht⟩:=ht.nonidentity_actor
  let q:=QuotientGroup.mk' (pCore 2 H)
  have hqne:q t≠1 := by
    intro he
    apply hn
    change a.action (q t)=1
    rw [he,map_one]
  have hsq:(t:G)^2=1 := by
    exact congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 P) (⟨t,htP⟩:P))
  have hqt:(q t)^2=1 := by
    rw [←map_pow]
    exact congrArg q (Subtype.ext hsq)
  have ho:orderOf (q t)=2:=orderOf_eq_prime hqt hqne
  obtain ⟨hA,hr,hquad,_⟩:=involution_actor_rank_and_fixedCodim (linearAction a) (q t) ho
  obtain ⟨f,z,hfz,he⟩:=ht
  have hform (v:Additive (U⧸Z.subgroupOf U)) : linearAction a (q t) v=v+f v•z := by
    change binaryLinear ((centerAction a).action t) v=_
    rw [he,LinearEquiv.transvection.apply]
  have hf:f≠0 := by
    intro hf
    apply hn
    ext v
    have hh:=hform (Additive.ofMul v)
    have hh':binaryLinear ((centerAction a).action t) (Additive.ofMul v)=Additive.ofMul v:=by
      change linearAction a (q t) (Additive.ofMul v)=_
      simpa [hf] using hh
    exact congrArg Additive.toMul hh'
  have hz:z≠0 := by
    intro hz
    apply hn
    ext v
    have hh:=hform (Additive.ofMul v)
    have hh':binaryLinear ((centerAction a).action t) (Additive.ofMul v)=Additive.ofMul v:=by
      change linearAction a (q t) (Additive.ofMul v)=_
      simpa [hz] using hh
    exact congrArg Additive.toMul hh'
  have hc:fixedCodim (linearAction a) (zpowers (q t))=1 := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    exact TransvectionRecognition.Component.transvection_displacement_rank ⟨f,z,hf,hz,hfz,hform⟩
  have hstar:Source.starImage H (zpowers (t:G))=zpowers (q t) := by
    unfold Source.starImage
    have hi:(zpowers (t:G)).subgroupOf H=zpowers t := by
      apply map_injective H.subtype_injective
      rw [map_subgroupOf_eq_of_le (zpowers_le.mpr t.property),MonoidHom.map_zpowers]
      rfl
    rw [hi,MonoidHom.map_zpowers]
  refine ⟨zpowers (t:G),zpowers_le.mpr htP,?_⟩
  rw [hstar]
  exact ⟨hA,hquad,by rw [hc,hr]; decide⟩

private theorem returned_core {L T H V:Subgroup G} (c:CriticalPair L T H V)
    (J P:Subgroup G) (he:(L⊔T)⊓H=J)
    (hP:P≤(edgeGroup L T H c.gamma c.previous).pCoreIn 2) :
    P.map (MulAut.conj (returnElement c:G)).toMonoidHom≤J.pCoreIn 2 := by
  have hedge:edgeGroup L T H c.gamma c.previous=J.map (MulAut.conj (c.gb:G)).toMonoidHom := by
    have hp:vertexGroup L T H c.previous=(L⊔T).map (MulAut.conj (c.gb:G)).toMonoidHom := by
      change vertexGroup L T H (c.path.getVert (c.path.length-1))=_
      rw [←c.gb_zero,vertexGroup_smul,vertexGroup_base]
      rfl
    change vertexGroup L T H c.gamma⊓vertexGroup L T H c.previous=_
    rw [c.vertexGroup_gamma,hp,←map_inf _ _ _ (MulAut.conj _).injective,inf_comm H,he]
  have hc:(edgeGroup L T H c.gamma c.previous).pCoreIn 2=(J.pCoreIn 2).map (MulAut.conj (c.gb:G)).toMonoidHom := by
    rw [hedge,map_pCoreIn_of_ker_isPGroup _ (IsPGroup.ker_isPGroup_of_injective (MulAut.conj _).injective)]
  have hh:=map_mono (f:=(MulAut.conj (returnElement c:G)).toMonoidHom) hP
  rw [hc] at hh
  exact hh.trans_eq (conjBy_inv (J.pCoreIn 2) (c.gb:G))

variable {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}
 (d:LocalSetup T L V V₁ V₂ V₃ M G₁)
 (hF9:(Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
 [IsElementaryAbelian 2 (Source.UH H V₃)]

include d hF9
theorem exists_edge_quadratic_actor :
    ∃ (a:Five.StarAction H (Source.UH H V₃) V₁) (B:Subgroup G),
      B≤((L⊔(T:Subgroup G))⊓H).pCoreIn 2 ∧
      QuadraticMember (linearAction a) (Source.starImage H B) := by
  let : IsElementaryAbelian 2 V:=hF9.elementary
  let dn:=localNaturalSetup d
  have hHG:H≤G₁ := by
    rw [dn.first_normalizer]
    exact hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  let : IsElementaryAbelian 2 (conjugateSpanBy V G₁):=d.span_elementary
  let : IsElementaryAbelian 2 (Source.VH H V):=
    IsElementaryAbelian.of_le (conjugateSpanBy_mono le_rfl hHG)
  have hz:H≤normalizer (V₁:Set G):=hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  have hQ:⁅Source.UH H V₃,Source.QH H⁆≤V₁:=hF9.commutator_UH_QH_le_point
  have hkernel:Source.QH H=commutatorPreimage H (Source.UH H V₃) V₁ := by
    have hh:=f9_commutatorPreimage_eq _ hF9 H le_rfl
    exact (hh.trans (inf_eq_right.mpr (map_subtype_le _))).symm
  obtain ⟨a,_⟩:=Five.exists_faithful_source_starAction H V₃ V₁ hz hkernel
  let act:SourceAction H V₃ V₁ := {
    line_le:=d.line_le_uh H
    seed_le:=hF9.plus_le_H
    representation:=linearAction a
    conjugation:=a.conjugation }
  let sec:=Comparison.sourceSection act hF9.H_centralizes
  have hcentral:⁅Source.VH H V,Source.HC H V₃⁆≤V₁ := by
    rw [commutator_comm]
    exact Section07.centralizer_UH_commutator dn hF9
  have hgeo:=local_earlierGeometry d hF9
  have hUV:Source.UH H V₃≤Source.VH H V:=conjugateSpanBy_mono d.seed_le le_rfl
  have he:=Comparison.local_edge d hF9
  have hfinish (c:CriticalPair L (T:Subgroup G) H V) (B:Subgroup G)
      (hB:B≤c.Vgamma) (hq:QuadraticMember (linearAction a) (Source.starImage H B)) :
      ∃B:Subgroup G,B≤((L⊔(T:Subgroup G))⊓H).pCoreIn 2 ∧
        QuadraticMember (linearAction a) (Source.starImage H B) := by
    have hcore:=(f9_endpoint_edge_cores _ hF9 c (hgeo c).length).2
    obtain ⟨h,_,hp,_⟩:=exists_second_to_base c (one L T V₁)
      ((one L T V₁⊔(T:Subgroup G)).pCoreIn 2) (by have:=(hgeo c).length; omega) he hcore le_rfl
    refine ⟨B.conjBy (h:G),?_,quadraticMember_conj (linearAction a) (hB.trans (hgeo c).Vgamma_H) hq h⟩
    rw [he]
    exact (map_mono hB).trans hp
  obtain ⟨c,_,_⟩:=dn.exists_criticalPair d.abelian_span hF9
  have hUgH:c.Ugamma V₃≤H:=(map_mono hUV).trans (hgeo c).Vgamma_H
  have hUA:Source.UH H V₃≤normalizer (c.Aone V₁:Set G):=
    (hUV.trans (hgeo c).VH_endpoint).trans (CriticalGeometry.SectionActions.CriticalPair.normalizes_Aone c V₁ hz)
  by_cases hDg:Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁<c.Ugamma V₃
  · by_cases hDH:Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)<Source.UH H V₃
    · obtain ⟨c',_,_,_,_,hq⟩:=dn.exists_quadratic_selection d.abelian_span hF9 sec c hDH hDg
      obtain ⟨B,hB,hq⟩:=hfinish c' (c'.Ugamma V₃) (map_mono hUV) hq
      exact ⟨a,B,hB,hq⟩
    · have hDH:=eq_of_le_of_not_lt (commutatorPreimage_le (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)) hDH
      have ht:=transvection_of_DH_eq_Dgamma_lt c V₃ V₁ (centerAction a) d.line_card hUgH hUA (hgeo c).lines_disjoint hDH hDg
      let : IsElementaryAbelian 2 (c.Ugamma V₃):=IsElementaryAbelian.map _
      obtain ⟨B,hB,hq⟩:=transvection_actor a ht
      obtain ⟨B,hB,hq⟩:=hfinish c B (hB.trans (map_mono hUV)) hq
      exact ⟨a,B,hB,hq⟩
  · have hDg:=eq_of_le_of_not_lt (commutatorPreimage_le (c.Ugamma V₃) (Source.UH H V₃) V₁) hDg
    have hbad:=f9_commutator_not_le_Aone _ hF9 c (hgeo c).length
    have hVcore:Source.VH H V≤(edgeGroup L (T:Subgroup G) H c.gamma c.previous).pCoreIn 2 := by
      have hh:=(f9_endpoint_edge_cores _ hF9 c (hgeo c).length).1
      change Source.VH H V≤(vertexGroup _ _ _ c.previous⊓vertexGroup _ _ _ c.gamma).pCoreIn 2 at hh
      rwa [inf_comm] at hh
    rcases transvection_of_Dgamma_eq c V₃ V₁ (centerAction a) d.seed_le hz d.line_card hUgH
      (hgeo c).VH_endpoint hUA (hgeo c).lines_disjoint hcentral hbad hDg with ht | ht
    · let : IsElementaryAbelian 2 (Ualpha c V₃):=IsElementaryAbelian.map _
      obtain ⟨B,hB,hq⟩:=transvection_actor a ht
      exact ⟨a,B,hB.trans (returned_core c _ _ rfl (hUV.trans hVcore)),hq⟩
    · let : IsElementaryAbelian 2 (Valpha c):=IsElementaryAbelian.map _
      obtain ⟨B,hB,hq⟩:=transvection_actor a ht
      exact ⟨a,B,hB.trans (returned_core c _ _ rfl hVcore),hq⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.F918
