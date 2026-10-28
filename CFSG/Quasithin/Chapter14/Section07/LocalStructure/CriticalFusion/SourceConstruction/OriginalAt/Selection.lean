module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CriticalSelection
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.NaturalAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Geometry

/-!
# Reciprocal path selection at the original G,T

A nonzero star image escapes the H-neighborhood kernel. Reverse the
actual path and retain both span and point markings. The two literal
indices interchange, so one orientation has the required rank comparison.
Source: AS F.9.17 and Notation 14.7.1, pp.324,1043.
The structural source producer remains qt-d-1222-source; final
14.7.75 discharge remains with qt-d-14775-source.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source Subgroup.CosetGeometry.RankTwo
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
local notation "S5" => ChapterJ.S5


omit [Finite G] in
private theorem conjBy_span_at (c:CriticalPath (L:=L) F)
    (k:GeometryGroup T L F) (hk:(k:G)=c.conjugator) (h t:F.H) :
    F.U.conjBy ((k:G)⁻¹*(h:G)*(t:G))=c.Uα := by
  have htU:F.U.conjBy (t:G)=F.U := mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy V F.H t.property)
  have hhU:F.U.conjBy (h:G)=F.U := mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy V F.H h.property)
  rw [conjBy_mul,conjBy_mul,htU,hhU,hk]
  rfl

omit [Finite G] in
private theorem point_conjBy_at (F:InvariantFlag T V 3) (h:F.H) :
    (F.Vi 1).conjBy (h:G)=F.Vi 1 :=
  mem_normalizer_iff_map_conj_eq.mp h.property

set_option backward.isDefEq.respectTransparency false in
theorem exists_reversal_of_star_ne_bot_at
    (natural:HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural:Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c:CriticalPath (L:=L) F) (hAH:c.Uα≤F.H) (hstar:star F c.Uα≠⊥) :
    Nonempty (SourceReversal.Geometry c) := by
  classical
  let K:=GeometryGroup T L F
  let Ω:=geometryFamily (L:=L) F
  let r:K:=inclusion (le_sup_right:F.H≤K) c.rechoice
  let k:K:=c.gammaConjugator*r
  let BK:=ballKernel Ω (base Ω true) 1
  have hk:(k:G)=c.conjugator := rfl
  have hnot:¬c.Uα≤BK.map K.subtype := by
    intro hh
    have hNH : BK.map K.subtype ≤ F.H := by
      have hs := map_mono (f := K.subtype) (ballKernel_le_stabilizer Ω (base Ω true) 1)
      exact hs.trans_eq (ChapterF.Section07.Geometry.base_stabilizer_map_true _ _)
    have hNLT : BK.map K.subtype ≤ L ⊔ (T : Subgroup G) := by
      have hadj : (graph Ω).Adj (base Ω true) (base Ω false) :=
        ⟨by change true ≠ false; decide, CosetGeometry.incident_base Ω true false⟩
      have hs := map_mono (f := K.subtype) ((ballKernel_one_le_edge Ω hadj).trans inf_le_right)
      exact hs.trans_eq (ChapterF.Section07.Geometry.base_stabilizer_map_false _ _)
    have hn : F.H ≤ normalizer (BK.map K.subtype : Set G) := by
      intro a ha
      let aK : K := ⟨a,mem_sup_right ha⟩
      have haK : aK ∈ stabilizer Ω (base Ω true) := by
        simpa only [stabilizer,base,CosetGeometry.stabilizer_base] using
          (show aK ∈ Ω true from ha)
      exact le_normalizer_map K.subtype (mem_map_of_mem K.subtype
        (stabilizer_le_normalizer_ballKernel Ω (base Ω true) 1 haK))
    have hc : c.Uα ≤ F.H.pCoreIn 2 :=
      ((le_inf hh (critical_le_Q_at natural structural c)).trans
        (inf_pCoreIn_le_of_le 2 hNLT)).trans (pCoreIn_mono_of_normalizes hNH hn)
    have hi:=CriticalIntersections.core_intersection_index_eq_star_card c.Uα hAH
    rw [inf_eq_right.mpr hc,relIndex_self] at hi
    exact hstar (card_eq_one.mp hi.symm)
  have hex:∃h:F.H,¬V.conjBy ((k:G)⁻¹*(h:G))≤BK.map K.subtype := by
    by_contra! hall
    apply hnot
    change F.U.map (MulAut.conj (k:G)⁻¹).toMonoidHom≤BK.map K.subtype
    apply (map_le_iff_le_comap).mpr
    apply (closure_le _).mpr
    rintro x ⟨h,hh,v,hv,rfl⟩
    have hm:=hall ⟨h,hh⟩ (mem_map_of_mem (MulAut.conj ((k:G)⁻¹*h)).toMonoidHom hv)
    change (MulAut.conj (k:G)⁻¹) (h*v*h⁻¹)∈BK.map K.subtype
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
    have hvK:v∈K:=((natural.chosen.le_sylow hvV):v∈(T:Subgroup G))|>
      ((le_sup_right:(T:Subgroup G)≤L⊔(T:Subgroup G)).trans le_sup_left)
    have hh: a*⟨v,hvK⟩*a⁻¹∈BK := by
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
    exact conjBy_span_at c k hk h tH
  have hxZ:conjugate (F.Vi 1) (c'.conjugator)⁻¹=c.Zα := by
    simp only [conjugate,inv_inv]
    change (F.Vi 1).conjBy (c'.conjugator)=c.Zα
    rw [hc']
    change (F.Vi 1).conjBy (((k:G)⁻¹*(h:G))*(tH:G))=c.Zα
    rw [conjBy_mul,conjBy_mul,point_conjBy_at F tH,point_conjBy_at F h,hk]
    rfl
  refine ⟨⟨c',c'.conjugator⁻¹,?_,hxU,?_,hxZ,?_⟩⟩
  · rw [hc']; exact K.inv_mem (a*t).property
  · simp only [conjugate,inv_inv]
    change (F.U.conjBy (c'.conjugator)⁻¹).conjBy c'.conjugator=F.U
    exact conjBy_inv' _ _
  · simp only [conjugate,inv_inv]
    change ((F.Vi 1).conjBy (c'.conjugator)⁻¹).conjBy c'.conjugator=F.Vi 1
    exact conjBy_inv' _ _

theorem select_critical_orientation_of_nontrivial_star_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (hstar : star F c.Uα ≠ ⊥) :
    ∃ a : CriticalPath (L := L) F, a.RankSelection := by
  classical
  by_cases hr : Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) ≤ Nat.log 2 (Nat.card (star F c.Uα))
  · exact ⟨c,⟨critical_index_positive c,hr⟩⟩
  have hAH : c.Uα ≤ F.H := (critical_le_Q_at h structural c).trans (Q_le_H F)
  obtain ⟨r⟩ := exists_reversal_of_star_ne_bot_at h structural c hAH hstar
  have hrAH : r.path.Uα ≤ F.H := (critical_le_Q_at h structural r.path).trans (Q_le_H F)
  refine ⟨r.path,⟨critical_index_positive r.path,?_⟩⟩
  rw [r.reverse_index_of_placement hAH,r.reverse_star_of_placement hrAH]
  exact Nat.le_of_lt (Nat.lt_of_not_ge hr)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
