module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.SourceReversal.Kernel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.Reversal

/-!
# Reverse the literal critical path with its two H adjustments

A nontrivial starred actor escapes the H neighborhood kernel. Since U is
its actual H-span, one original V conjugate detects a neighbor. Reverse the
recorded tail, add that edge, and normalize its initial edge. The fixed-ball
radius proves the resulting walk geodesic. A separate H adjustment marks
its second vertex. Both adjustments normalize U and the central point,
which yields the four literal subgroup markings required by14.7.39.

No swapping element or preselected reversed path is assumed.
Source: Aschbacher–Smith F.9.17 and14.7.39, pp.324 and1060.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.SourceReversal
open Chapter12.Section08 Subgroup.CosetGeometry.RankTwo
universe u
variable {G:Type u} [Group G] [Finite G] {T:Sylow 2 G} {L V:Subgroup G}
 {F:InvariantFlag T V 3} {W:Type u} [AddCommGroup W] [Module (ZMod 2) W]

structure Geometry (c:CriticalPath (L:=L) F) where
  path:CriticalPath (L:=L) F
  conjugator:G
  conjugator_mem:conjugator∈GeometryGroup T L F
  base_U:conjugate F.U conjugator=c.Uα
  tip_U:conjugate path.Uα conjugator=F.U
  base_point:conjugate (F.Vi 1) conjugator=c.Zα
  tip_point:conjugate path.Zα conjugator=F.Vi 1

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
theorem exists_geometry (d:Data T L V F W)
    (structural:Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c:CriticalPath (L:=L) F) (earlier:c.EarlierImages) (selection:c.RankSelection) :
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
    have hc:=hh.trans (H_kernel_le_core d structural)
    have hi:=CriticalIntersections.core_intersection_index_eq_star_card c.Uα (c.Uα_le_H earlier)
    rw [inf_eq_right.mpr hc,relIndex_self] at hi
    exact c.star_ne_bot selection (card_eq_one.mp hi.symm)
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
