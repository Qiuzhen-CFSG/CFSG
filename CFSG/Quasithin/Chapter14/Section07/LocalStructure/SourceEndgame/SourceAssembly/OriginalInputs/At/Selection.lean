module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.CriticalGeometry
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.PointCommutator
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.CriticalSelection.Source

/-!
# Selected critical path from the original ambient source inputs

The natural action, original section and unique escaping local subgroup
supply F.8 on the literal LT/H graph. Its geodesic gives the first critical
path. The point commutator excludes trivial star image, and the reverse
path with two actual H adjustments interchanges the comparison ranks.
Choosing its orientation constructs both rank-selection clauses.

The final application consumes original 13.3.2(3) at G,T,L, constructing
the point commutator internally. Only that earlier module theorem and
Structural1222At remain explicit. Producers qt-d-1332-source and
qt-d-1222-source retain these inputs; final original 14.7.75 discharge
remains with qt-d-14775-source. No critical path, escape or rank comparison
is assumed. Source: AS 14.5.18(4–5), 14.5.21(2), Notation 14.7.1 and F.9.17.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.CriticalSelection
open Chapter12.Section08
universe u
variable {G:Type u} [Group G] [Finite G] {T:Sylow 2 G} {L V:Subgroup G}
 {F:InvariantFlag T V 3} {W:Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- Original F8 hypotheses on the actual LT/H pair. -/
theorem f8_hypothesis_at (d:Data T L V F W)
    (structural:Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    ChapterF.Section08.Setup.Hypothesis (F.f8SourceSetup L F.H) := by
  let := d.natural.chosen.elementary
  have hJ : F.H∈F.Hz L (normalizer (L:Set G)) := by
    rw [d.unique_Hz]
    exact Set.mem_singleton _
  have hzV : d.z∈V := F.le_seed 1 (d.point ▸ mem_zpowers d.z)
  apply F.f8Source_hypothesis d.natural.source.simpleQTKE L (normalizer (L:Set G))
    (by decide) d.natural.chosen.le_sylow d.natural.chosen.normalizes
    (d.natural.sylow_normalizes_at structural) d.natural.residual
    (fun _=>⟨d.natural.naturalMarking⟩) rfl
    (d.natural.maximal_unique_at structural).2
    ((Subgroup.centralizer_le_normalizer _).trans (d.natural.seed_normalizer_le_at structural)) d.natural.centralizer_L
    d.natural.source.maximal_faithful.2.1.2.2 (((structural L d.natural.source).2.2 V d.natural.chosen).2.1)
    (d.natural.centralizer_LT_at structural) d.z d.point d.z_ne_one _ d.abelian F.H hJ
  intro x hx hx1
  obtain ⟨l,hl,he⟩ := d.natural.vector_transitive hzV hx d.z_ne_one hx1
  exact ⟨l,d.natural.chosen.normalizes hl,he⟩

open Subgroup.CosetGeometry.RankTwo

set_option backward.isDefEq.respectTransparency false in
/-- First critical path and the actual H adjustment. -/
theorem exists_criticalPath_at (d:Data T L V F W)
    (structural:Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    Nonempty (CriticalPath (L:=L) F) := by
  classical
  let D:=F.f8SourceSetup L F.H
  let h:ChapterF.Section08.Setup.Hypothesis D:=f8_hypothesis_at d structural
  obtain ⟨C⟩:=h.exists_criticalPath
  let Ω:=geometryFamily (L:=L) F
  let a:GeometryGroup T L F:=C.g⁻¹
  have he:C.endpoint=a⁻¹ • base Ω true := by
    change C.endpoint=(C.g⁻¹)⁻¹ • base (ChapterF.Section08.Setup.Hypothesis.family (D:=D)) true
    rw [inv_inv]
    exact C.endpoint_eq.symm
  let p:(graph Ω).Walk (base Ω false) (a⁻¹ • base Ω true):=C.path.copy rfl he
  have hlen:p.length=h.b := by
    dsimp only [p]
    rw [SimpleGraph.Walk.length_copy]
    exact C.shortest.trans C.distance
  have hfirst:p.getVert 1=base Ω true := by
    dsimp only [p]
    rw [SimpleGraph.Walk.getVert_copy]
    exact C.first
  have hadj₂:(graph Ω).Adj (base Ω true) (p.getVert 2) := by
    have hh:=p.adj_getVert_succ (i:=1) (by rw [hlen]; have := h.lemma_F_8_5.1; omega)
    rwa [hfirst] at hh
  obtain ⟨t,ht,hte⟩:=locally_transitive Ω
    (show (graph Ω).Adj (base Ω true) (base Ω false) from
      ⟨by change true≠false; decide,CosetGeometry.incident_base Ω true false⟩) hadj₂
  have htH:(t:G)∈F.H := by
    have ht':t∈Ω true := by simpa only [stabilizer,CosetGeometry.stabilizer_base] using ht
    exact ht'
  refine ⟨{
    b:=h.b
    radius:=?_
    gammaConjugator:=a
    path:=p
    geodesic:=?_
    length:=hlen
    first:=hfirst
    critical:=?_
    rechoice:=⟨t,htH⟩
    alignment:=?_ }⟩
  · intro n
    have hh:=(h.f7Setup.track_spec h.f7V_ne_bot).2.2.2 n
    rw [h.f7Seed_eq] at hh
    exact hh
  · dsimp only [p]
    rw [SimpleGraph.Walk.length_copy,←he]
    exact C.shortest
  · have hh:=C.critical
    rw [h.f7Seed_eq] at hh
    change ¬ V.subgroupOf (GeometryGroup T L F)≤ballKernel Ω C.endpoint 1 at hh
    rw [he] at hh
    exact hh
  · change t⁻¹ • p.getVert 2=base Ω false
    rw [←hte,inv_smul_smul]
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.CriticalSelection

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
open Subgroup Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
include d in
theorem critical_star_nontrivial_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hUQ : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (c : CriticalPath (L:=L) F) : star F c.Uα ≠ ⊥ := by
  intro hz
  have hAH : c.Uα ≤ F.H := (d.source_critical_le_Q_at structural c).trans (Q_le_H F)
  have hαQ : c.Uα ≤ F.H.pCoreIn 2 := by
    have hk : c.Uα.subgroupOf F.H ≤ pCore 2 F.H := by
      simpa only [star,Subgroup.map_eq_bot_iff,starMap,QuotientGroup.ker_mk'] using hz
    intro x hx
    exact mem_map.mpr ⟨⟨x,hAH hx⟩,hk hx,rfl⟩
  let f := (MulAut.conj c.conjugator).toMonoidHom
  let A := F.U.map f
  let C := (F.Vi 1).map f
  have hmap : c.Uα.map f=F.U := by
    change (F.U.conjBy c.conjugator⁻¹).conjBy c.conjugator=F.U
    exact conjBy_inv' _ _
  have hA : A ≤ F.H := by
    have h := map_mono (f:=f) (d.source_reciprocal_placement c)
    change A ≤ (F.H.conjBy c.conjugator⁻¹).conjBy c.conjugator at h
    rwa [conjBy_inv'] at h
  have hc : ⁅A,F.U⁆ ≤ C := by
    have h := map_mono (f:=f) ((commutator_mono le_rfl hαQ).trans_eq hUQ)
    rwa [map_commutator,hmap] at h
  have hcard : Nat.card C ≤ 2 := by
    rw [show Nat.card C=Nat.card (F.Vi 1) from card_map_of_injective
      (MulAut.conj c.conjugator).injective]
    exact (show Nat.card (F.Vi 1)=2 by simpa using F.card 1 (by decide)).le
  have hAQ : A ≤ F.H.pCoreIn 2 := by
    intro x hx
    exact d.actor_in_core_of_small_commutator A C hc hcard ⟨x,hA hx⟩ hx
  apply d.critical_span_not_le_reciprocal_core c
  intro x hx
  change x ∈ (conjugate F.H c.conjugator).pCoreIn 2
  unfold conjugate
  rw [← map_pCoreIn_of_injective 2 F.H (MulAut.conj c.conjugator⁻¹).toMonoidHom
    (MulAut.conj c.conjugator⁻¹).injective]
  refine ⟨f x,hAQ (mem_map_of_mem f hx),?_⟩
  simp [f,MulAut.conj_apply,mul_assoc]
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
public section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.SourceReversal
open Subgroup Chapter12.Section08 Subgroup.CosetGeometry.RankTwo
universe u
variable {G:Type u} [Group G] [Finite G] {T:Sylow 2 G} {L V:Subgroup G}
 {F:InvariantFlag T V 3} {W:Type u} [AddCommGroup W] [Module (ZMod 2) W]
private theorem conjBy_span (d:Data T L V F W) (c:CriticalPath (L:=L) F)
    (k:GeometryGroup T L F) (hk:(k:G)=c.conjugator) (h t:F.H) :
    F.U.conjBy ((k:G)⁻¹*(h:G)*(t:G))=c.Uα := by
  have htU:F.U.conjBy (t:G)=F.U := mem_normalizer_iff_map_conj_eq.mp (d.conjugationSection.normalized t.property)
  have hhU:F.U.conjBy (h:G)=F.U := mem_normalizer_iff_map_conj_eq.mp (d.conjugationSection.normalized h.property)
  rw [conjBy_mul,conjBy_mul,htU,hhU,hk]
  rfl

omit [Finite G] in
private theorem point_conjBy (F:InvariantFlag T V 3) (h:F.H) :
    (F.Vi 1).conjBy (h:G)=F.Vi 1 :=
  mem_normalizer_iff_map_conj_eq.mp h.property

set_option backward.isDefEq.respectTransparency false in
/-- The two adjustments are chosen in the original H and both endpoints retain
 their actual U and point markings. -/
theorem exists_geometry_of_star_ne_bot_at (d:Data T L V F W)
    (structural:Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c:CriticalPath (L:=L) F) (hAH:c.Uα≤F.H) (hstar:star F c.Uα≠⊥) :
    Nonempty (Geometry c) := by
  classical
  let K:=GeometryGroup T L F
  let Ω:=geometryFamily (L:=L) F
  let r:K:=inclusion (le_sup_right:F.H≤K) c.rechoice
  let k:K:=c.gammaConjugator*r
  let B:=ballKernel Ω (base Ω true) 1
  have hk:(k:G)=c.conjugator := rfl
  have hnot:¬c.Uα≤B.map K.subtype := by
    intro hh
    have hc:=hh.trans (H_kernel_le_core_at d structural)
    have hi:=CriticalIntersections.core_intersection_index_eq_star_card c.Uα hAH
    rw [inf_eq_right.mpr hc,relIndex_self] at hi
    exact hstar (card_eq_one.mp hi.symm)
  have hex:∃h:F.H,¬V.conjBy ((k:G)⁻¹*(h:G))≤B.map K.subtype := by
    by_contra! hall
    apply hnot
    change F.U.map (MulAut.conj (k:G)⁻¹).toMonoidHom≤B.map K.subtype
    apply (map_le_iff_le_comap).mpr
    apply (closure_le _).mpr
    rintro x ⟨h,hh,v,hv,rfl⟩
    have hm:=hall ⟨h,hh⟩ (mem_map_of_mem (MulAut.conj ((k:G)⁻¹*h)).toMonoidHom hv)
    change (MulAut.conj (k:G)⁻¹) (h*v*h⁻¹)∈B.map K.subtype
    simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,mul_inv_rev,mul_assoc,inv_inv] using hm
  obtain ⟨h,hbad⟩:=hex
  let a:K:=k⁻¹*inclusion (le_sup_right:F.H≤K) h
  let α:=k⁻¹ • base Ω true
  have ha:a • base Ω true=α := by
    have hh:(inclusion (le_sup_right:F.H≤K) h) • base Ω true=base Ω true := by
      apply MulAction.mem_stabilizer_iff.mp
      simpa only [CosetGeometry.stabilizer_base] using (show inclusion (le_sup_right:F.H≤K) h∈Ω true from h.property)
    simp only [a,mul_smul,hh,α]
  have hadj:(graph Ω).Adj (a • base Ω false) α := by
    rw [←ha]
    exact (CosetGeometry.translationGraphIso Ω a).toHom.map_adj
      ⟨by change false≠true; decide,CosetGeometry.incident_base Ω false true⟩
  have hrH:r⁻¹ • base Ω true=base Ω true := by
    have hr:r • base Ω true=base Ω true := by
      apply MulAction.mem_stabilizer_iff.mp
      simpa only [CosetGeometry.stabilizer_base] using (show r∈Ω true from c.rechoice.property)
    exact (congrArg (r⁻¹ • ·) hr).symm.trans (inv_smul_smul r _)
  let tail: (graph Ω).Walk α (base Ω true) :=
    ((((c.path.drop 1).copy c.first rfl).reverse).map
      (CosetGeometry.translationGraphIso Ω r⁻¹).toHom).copy
        (by change r⁻¹ • (c.gammaConjugator⁻¹ • base Ω true)=α; simp only [α,k,mul_inv_rev,mul_smul]) hrH
  let p := tail.cons hadj
  let w:(graph Ω).Walk (base Ω false) (a⁻¹ • base Ω true) :=
    (p.map (CosetGeometry.translationGraphIso Ω a⁻¹).toHom).copy (inv_smul_smul a _) rfl
  have hplen:p.length=c.b := by
    simp only [p,tail,SimpleGraph.Walk.length_cons,SimpleGraph.Walk.length_copy,
      SimpleGraph.Walk.length_map,SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.drop_length,c.length]
    have := c.three_le; omega
  have hwlen:w.length=c.b := by
    simp only [w,SimpleGraph.Walk.length_copy,SimpleGraph.Walk.length_map,hplen]
  have hwfirst:w.getVert 1=base Ω true := by
    simp only [w,SimpleGraph.Walk.getVert_copy,SimpleGraph.Walk.getVert_map,p,
      SimpleGraph.Walk.getVert_cons_succ,SimpleGraph.Walk.getVert_zero,←ha]
    exact inv_smul_smul a _
  have hcrit:¬V.subgroupOf K≤ballKernel Ω (a⁻¹ • base Ω true) 1 := by
    intro hv
    apply hbad
    rintro x ⟨v,hvV,rfl⟩
    have hvK:v∈K:=((d.natural.chosen.le_sylow hvV):v∈(T:Subgroup G))|>
      ((le_sup_right:(T:Subgroup G)≤L⊔(T:Subgroup G)).trans le_sup_left)
    have hh: a*⟨v,hvK⟩*a⁻¹∈B := by
      have hh:=(conj_mem_ballKernel_iff Ω a (⟨v,hvK⟩:K) (a⁻¹ • base Ω true) 1).mpr (hv hvV)
      simpa only [smul_inv_smul] using hh
    exact ⟨a*⟨v,hvK⟩*a⁻¹,hh,rfl⟩
  have hgeo:w.length=(graph Ω).dist (base Ω false) (a⁻¹ • base Ω true) := by
    apply le_antisymm _ (SimpleGraph.dist_le w)
    rw [hwlen]
    exact ChapterF.Section07.Track.critical_distance_minimal Ω
      (ChapterF.Section07.Geometry.family_generates _ _) ((c.radius c.b).mpr le_rfl) hcrit
  have hadj₂:(graph Ω).Adj (base Ω true) (w.getVert 2) := by
    have hh:=w.adj_getVert_succ (i:=1) (by rw [hwlen]; have := c.three_le; omega)
    rwa [hwfirst] at hh
  obtain ⟨t,ht,hte⟩:=locally_transitive Ω
    (show (graph Ω).Adj (base Ω true) (base Ω false) from
      ⟨by change true≠false; decide,CosetGeometry.incident_base Ω true false⟩) hadj₂
  have htH:(t:G)∈F.H := by
    have ht':t∈Ω true := by simpa only [stabilizer,CosetGeometry.stabilizer_base] using ht
    exact ht'
  let tH:F.H:=⟨t,htH⟩
  let c':CriticalPath (L:=L) F := {
    b:=c.b
    radius:=c.radius
    gammaConjugator:=a
    path:=w
    geodesic:=hgeo
    length:=hwlen
    first:=hwfirst
    critical:=hcrit
    rechoice:=tH
    alignment:=by
      change t⁻¹ • w.getVert 2=base Ω false
      rw [←hte,inv_smul_smul] }
  have hc':c'.conjugator=(a*t:G) := rfl
  have hxU:conjugate F.U (c'.conjugator)⁻¹=c.Uα := by
    simp only [conjugate,inv_inv]
    change F.U.conjBy (c'.conjugator)=c.Uα
    rw [hc']
    exact conjBy_span d c k hk h tH
  have hxZ:conjugate (F.Vi 1) (c'.conjugator)⁻¹=c.Zα := by
    simp only [conjugate,inv_inv]
    change (F.Vi 1).conjBy (c'.conjugator)=c.Zα
    rw [hc']
    change (F.Vi 1).conjBy (((k:G)⁻¹*(h:G))*(tH:G))=c.Zα
    rw [conjBy_mul,conjBy_mul,point_conjBy F tH,point_conjBy F h,hk]
    rfl
  refine ⟨⟨c',c'.conjugator⁻¹,?_,hxU,?_,hxZ,?_⟩⟩
  · rw [hc']; exact K.inv_mem (a*t).property
  · simp only [conjugate,inv_inv]
    change (F.U.conjBy (c'.conjugator)⁻¹).conjBy c'.conjugator=F.U
    exact conjBy_inv' _ _
  · simp only [conjugate,inv_inv]
    change ((F.Vi 1).conjBy (c'.conjugator)⁻¹).conjBy c'.conjugator=F.Vi 1
    exact conjBy_inv' _ _
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.SourceReversal
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
open Subgroup Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
variable (d : Data T L V F W)

include d in
theorem select_critical_orientation_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hUQ : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (c : CriticalPath (L:=L) F) :
    ∃ a : CriticalPath (L:=L) F, a.RankSelection := by
  classical
  have hp := d.critical_index_positive c
  by_cases hr : Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) ≤ Nat.log 2 (Nat.card (star F c.Uα))
  · exact ⟨c,⟨hp,hr⟩⟩
  have hAH : c.Uα ≤ F.H := (d.source_critical_le_Q_at structural c).trans (Q_le_H F)
  obtain ⟨r⟩ := SourceReversal.exists_geometry_of_star_ne_bot_at d structural c hAH
    (d.critical_star_nontrivial_at structural hUQ c)
  have hrAH : r.path.Uα ≤ F.H :=
    (d.source_critical_le_Q_at structural r.path).trans (Q_le_H F)
  refine ⟨r.path,⟨d.critical_index_positive r.path,?_⟩⟩
  rw [r.reverse_index_of_placement hAH,r.reverse_star_of_placement hrAH]
  exact Nat.le_of_lt (Nat.lt_of_not_ge hr)
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
open Subgroup Chapter12.Section08 Chapter13.Section03.SourceCompletion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
include d

/-- Construct the actual selected path using only the original local inputs. -/
theorem exists_selected_criticalPath_from_original_modules_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (five : OriginalAlternatingFiveModules1332At T L) :
    ∃ c : CriticalPath (L := L) F, c.RankSelection := by
  obtain ⟨c⟩ := CriticalSelection.exists_criticalPath_at d structural
  exact d.select_critical_orientation_at structural
    (d.U_core_commutator_eq_point_of_original_modules_at five) c

/-- The constructed selection feeds the original order-two/full-image reduction. -/
theorem exists_order_two_or_full_criticalPath_from_original_modules_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (five : OriginalAlternatingFiveModules1332At T L)
    (himage : star F (Q T L) = star F (F.Ri L 1))
    (hsylow : Chapter1.IsSylowIn 2 (star F (F.Ri L 1)) (star F (K F))) :
    ∃ c : CriticalPath (L := L) F, c.EarlierImages ∧ c.RankSelection ∧
      (Nat.card (star F c.Uα) = 2 ∨ star F c.Uα = star F (Q T L)) := by
  obtain ⟨c,hs⟩ := d.exists_selected_criticalPath_from_original_modules_at structural five
  have he := d.source_earlierImages_at structural c himage hsylow
  exact ⟨c,he,hs,c.order_two_or_full d he hs⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
