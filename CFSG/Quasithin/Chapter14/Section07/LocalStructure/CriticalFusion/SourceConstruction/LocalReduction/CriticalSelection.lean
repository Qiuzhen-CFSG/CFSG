module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CriticalActors
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.CriticalSelection.Orientation
public import Theory.GroupTheory.PCoreImage

/-!
# Select the original critical rank comparison before recognition

The H-neighborhood kernel is normal in H and contained in LT. Its
intersection with Q lies in its own two-core and hence in O₂(H). Thus
an original critical actor in Q with nontrivial star image escapes that
neighborhood kernel. This constructs the reverse critical path with both original
span and central-point markings. The existing literal-index transports
interchange its two ranks, so one orientation satisfies Notation 14.7.1.

The same point-core marking bounds every critical actor's order by four.
The final application constructs a selected path with positive reciprocal
rank, the actual comparison, reciprocal placement, and actor rank at most
two. The offender bound and its equality case, natural recognition, and the
remaining residual classification are not asserted here.

Source: Aschbacher–Smith, F.9.17, 14.5.18(4–5), Notation 14.7.1,
and the concluding proof of 14.7.40, printed pp.324,1018,1043,1063.
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
private theorem conjBy_span (c:CriticalPath (L:=L) F)
    (k:GeometryGroup T L F) (hk:(k:G)=c.conjugator) (h t:F.H) :
    F.U.conjBy ((k:G)⁻¹*(h:G)*(t:G))=c.Uα := by
  have htU:F.U.conjBy (t:G)=F.U := mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy V F.H t.property)
  have hhU:F.U.conjBy (h:G)=F.U := mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy V F.H h.property)
  rw [conjBy_mul,conjBy_mul,htU,hhU,hk]
  rfl

omit [Finite G] in
private theorem point_conjBy (F:InvariantFlag T V 3) (h:F.H) :
    (F.Vi 1).conjBy (h:G)=F.Vi 1 :=
  mem_normalizer_iff_map_conj_eq.mp h.property

set_option backward.isDefEq.respectTransparency false in
/-- The two adjustments are chosen in the original H and both endpoints retain
 their actual U and point markings. -/
theorem exists_reversal_of_star_ne_bot
    (natural:HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural:Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
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
      ((le_inf hh (critical_le_Q natural structural c)).trans
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
    exact conjBy_span c k hk h tH
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


/-- Nontrivial critical images suffice to orient the actual reciprocal pair;
no identification of the full star quotient is used. -/
theorem select_critical_orientation_of_nontrivial_star
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) (hstar : star F c.Uα ≠ ⊥) :
    ∃ a : CriticalPath (L := L) F, a.RankSelection := by
  classical
  by_cases hr : Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) ≤ Nat.log 2 (Nat.card (star F c.Uα))
  · exact ⟨c,⟨critical_index_positive c,hr⟩⟩
  have hAH : c.Uα ≤ F.H := (critical_le_Q h structural c).trans (Q_le_H F)
  obtain ⟨r⟩ := exists_reversal_of_star_ne_bot h structural c hAH hstar
  have hrAH : r.path.Uα ≤ F.H := (critical_le_Q h structural r.path).trans (Q_le_H F)
  refine ⟨r.path,⟨critical_index_positive r.path,?_⟩⟩
  rw [r.reverse_index_of_placement hAH,r.reverse_star_of_placement hrAH]
  exact Nat.le_of_lt (Nat.lt_of_not_ge hr)

/-- Choose the original path or its explicitly constructed reverse. Both
quotient indices use the same original U/V₁ conjugation action. -/
theorem select_critical_orientation
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : HStar F.H ≃* S5) (c : CriticalPath (L := L) F) :
    ∃ a : CriticalPath (L := L) F, a.RankSelection := by
  exact select_critical_orientation_of_nontrivial_star h structural c
    (critical_star_nontrivial h hab structural e c)

/-- The point core is a literal four-group in the original star quotient. -/
theorem point_core_star_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : HStar F.H ≃* S5) : Nat.card (star F (F.Ri L 1)) = 4 := by
  have hm : (star F (F.Ri L 1)).map e.toMonoidHom =
      ((F.Ri L 1).subgroupOf F.H).map (quotientMarking e) := by
    rw [CriticalFusion.Source.star,map_map]
    rfl
  rw [←card_map_of_injective (K:=star F (F.Ri L 1)) (f:=e.toMonoidHom) e.injective,
    hm,point_core_image_card h structural e]

/-- Before natural recognition, every critical actor in the alternating
branch has rank one or two. -/
theorem critical_actor_rank
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : HStar F.H ≃* S5) (c : CriticalPath (L := L) F) :
    Nat.log 2 (Nat.card (star F c.Uα)) = 1 ∨
      Nat.log 2 (Nat.card (star F c.Uα)) = 2 := by
  have hle : star F c.Uα ≤ star F (F.Ri L 1) :=
    map_mono (comap_mono (critical_le_Ri h structural c))
  have hd := card_dvd_of_le hle
  rw [point_core_star_card h structural e] at hd
  have hn : 1 < Nat.card (star F c.Uα) :=
    (one_lt_card_iff_ne_bot _).mpr (critical_star_nontrivial h hab structural e c)
  have hd' : Nat.card (star F c.Uα) ∣ 2^2 := hd
  obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd'
  interval_cases k <;> norm_num at he <;> simp_all <;> decide

/-- The genuine critical rank comparison on the selected original path,
including the source bound k ≤ 2. No natural-module identification is used. -/
theorem exists_selected_critical_geometry_of_alternating
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hAlt : AlternatingResidual F) :
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧
      c.Uα ≤ F.Ri L 1 ∧ F.U ≤ conjugate F.H c.conjugator ∧
      Nat.log 2 (Nat.card (star F c.Uα)) ≤ 2 := by
  obtain ⟨c⟩ := exists_criticalPath_of_alternating h hab structural hAlt
  obtain ⟨e⟩ := exists_symmetric_star h structural hAlt
  obtain ⟨a,ha⟩ := select_critical_orientation h hab structural e c
  refine ⟨a,ha,critical_le_Ri h structural a,G2Source.reciprocal_placement h a,?_⟩
  rcases critical_actor_rank h hab structural e a with he | he <;> omega

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
