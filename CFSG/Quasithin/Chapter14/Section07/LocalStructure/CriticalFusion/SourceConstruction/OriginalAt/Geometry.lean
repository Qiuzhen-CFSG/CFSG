module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CriticalGeometry
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.NaturalAt

/-!
# The critical path before recognition at the original G,T

The local natural action supplies F.8 and its actual critical path.
The first-neighborhood kernel centralizes V, hence lies in O₂(LT);
transporting the terminal tail places the original critical actor in R₁.
No Data or star-quotient recognition is assumed.
Source: AS F.8.4–5, F.9.13–14 and 14.5.18, pp.316–317,322–323,1018.
The structural source producer remains qt-d-1222-source; final
14.7.75 discharge remains with qt-d-14775-source.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}


theorem f8_hypothesis_at (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (structural:Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    ChapterF.Section08.Setup.Hypothesis (F.f8SourceSetup L F.H) := by
  let := h.chosen.elementary
  obtain ⟨z, hz, he⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hJ := F.H_mem_Hz (by decide) L (normalizer (L : Set G)) hescape
  have hzV : z ∈ V := F.le_seed 1 (he.symm ▸ mem_zpowers z)
  apply F.f8Source_hypothesis h.source.simpleQTKE L (normalizer (L:Set G))
    (by decide) h.chosen.le_sylow h.chosen.normalizes
    (h.sylow_normalizes_at structural) h.residual
    (fun _=>⟨h.naturalMarking⟩) rfl
    (h.maximal_unique_at structural).2
    (Subgroup.centralizer_le_normalizer _ |>.trans (h.seed_normalizer_le_at structural)) h.centralizer_L
    h.source.maximal_faithful.2.1.2.2 ((structural L h.source).2.2 V h.chosen).2.1
    (h.centralizer_LT_at structural) z he hz _ hab F.H hJ
  intro x hx hx1
  obtain ⟨l,hl,he⟩ := h.vector_transitive hzV hx hz hx1
  exact ⟨l,h.chosen.normalizes hl,he⟩

open Subgroup.CosetGeometry.RankTwo

set_option backward.isDefEq.respectTransparency false in
theorem exists_criticalPath_at (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (structural:Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    Nonempty (CriticalPath (L:=L) F) := by
  classical
  let D:=F.f8SourceSetup L F.H
  let hf:ChapterF.Section08.Setup.Hypothesis D:=f8_hypothesis_at h hab hescape structural
  obtain ⟨C⟩:=hf.exists_criticalPath
  let Ω:=geometryFamily (L:=L) F
  let a:GeometryGroup T L F:=C.g⁻¹
  have he:C.endpoint=a⁻¹ • base Ω true := by
    change C.endpoint=(C.g⁻¹)⁻¹ • base (ChapterF.Section08.Setup.Hypothesis.family (D:=D)) true
    rw [inv_inv]
    exact C.endpoint_eq.symm
  let p:(graph Ω).Walk (base Ω false) (a⁻¹ • base Ω true):=C.path.copy rfl he
  have hlen:p.length=hf.b := by
    dsimp only [p]
    rw [SimpleGraph.Walk.length_copy]
    exact C.shortest.trans C.distance
  have hfirst:p.getVert 1=base Ω true := by
    dsimp only [p]
    rw [SimpleGraph.Walk.getVert_copy]
    exact C.first
  have hadj₂:(graph Ω).Adj (base Ω true) (p.getVert 2) := by
    have hh:=p.adj_getVert_succ (i:=1) (by rw [hlen]; have := hf.lemma_F_8_5.1; omega)
    rwa [hfirst] at hh
  obtain ⟨t,ht,hte⟩:=locally_transitive Ω
    (show (graph Ω).Adj (base Ω true) (base Ω false) from
      ⟨by change true≠false; decide,CosetGeometry.incident_base Ω true false⟩) hadj₂
  have htH:(t:G)∈F.H := by
    have ht':t∈Ω true := by simpa only [stabilizer,CosetGeometry.stabilizer_base] using ht
    exact ht'
  refine ⟨{
    b:=hf.b
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
    have hh:=(hf.f7Setup.track_spec hf.f7V_ne_bot).2.2.2 n
    rw [hf.f7Seed_eq] at hh
    exact hh
  · dsimp only [p]
    rw [SimpleGraph.Walk.length_copy,←he]
    exact C.shortest
  · have hh:=C.critical
    rw [hf.f7Seed_eq] at hh
    change ¬ V.subgroupOf (GeometryGroup T L F)≤ballKernel Ω C.endpoint 1 at hh
    rw [he] at hh
    exact hh
  · change t⁻¹ • p.getVert 2=base Ω false
    rw [←hte,inv_smul_smul]

theorem base_kernel_le_Q_at (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    (ballKernel (geometryFamily (L := L) F)
      (base (geometryFamily (L := L) F) false) 1).map (GeometryGroup T L F).subtype ≤ Q T L := by
  obtain ⟨z, hz, hpoint⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hcenter := F.H_eq_centralizer (by decide) z hpoint
  let K := GeometryGroup T L F
  let Ω := geometryFamily (L := L) F
  intro x hx
  obtain ⟨x,hx,rfl⟩ := hx
  have hxM : (x:G) ∈ L ⊔ (T : Subgroup G) := by
    have hh := ballKernel_le_stabilizer Ω (base Ω false) 1 hx
    have hh' : x ∈ Ω false := by simpa only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base] using hh
    exact hh'
  change (x:G) ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2
  rw [← h.centralizer_LT_at structural]
  refine ⟨hxM,?_⟩
  intro v hv
  by_cases h1 : v=1
  · simp [h1]
  have hzV : z ∈ V := F.le_seed 1 (hpoint.symm ▸ mem_zpowers z)
  obtain ⟨l,hl,he⟩ := h.vector_transitive hzV hv hz h1
  let l' : K := ⟨l,(le_sup_left : L ≤ L ⊔ (T:Subgroup G)).trans le_sup_left hl⟩
  have hlfix : l' • base Ω false = base Ω false := by
    apply MulAction.mem_stabilizer_iff.mp
    have hh : l' ∈ Ω false := mem_sup_left hl
    simpa only [Subgroup.CosetGeometry.stabilizer_base] using hh
  have hneigh : (graph Ω).Adj (base Ω false) (l' • base Ω true) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso Ω l').toHom.map_adj
      (show (graph Ω).Adj (base Ω false) (base Ω true) from
        ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base Ω false true⟩)
    change (graph Ω).Adj (l' • base Ω false) (l' • base Ω true) at hh
    simpa only [hlfix] using hh
  have hefix := hx (l' • base Ω true) ((mem_ball_one Ω _ _).mpr (Or.inl hneigh))
  have hm : l'⁻¹*x*l' ∈ Ω true := by
    have hh : l'⁻¹*x*l' ∈ stabilizer Ω (base Ω true) := by
      change (l'⁻¹*x*l') • base Ω true = base Ω true
      rw [mul_smul,mul_smul,hefix,inv_smul_smul]
    simpa only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base] using hh
  have hc : l⁻¹*(x:G)*l ∈ centralizer ({z} : Set G) := by
    rw [←hcenter]
    exact hm
  have hz := mem_centralizer_singleton_iff.mp hc
  have hh := congrArg (fun y : G => l*y*l⁻¹) hz
  have hv' : l*z*l⁻¹ = v := he
  have heq : (x:G)*(l*z*l⁻¹)=(l*z*l⁻¹)*(x:G) := by
    simpa only [mul_assoc,mul_inv_cancel_left,inv_mul_cancel_right,mul_inv_cancel,mul_one] using hh
  rw [hv'] at heq
  exact heq.symm

theorem critical_le_Q_at (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) : c.Uα ≤ Q T L := by
  let K := GeometryGroup T L F
  let Ω := geometryFamily (L := L) F
  let r : K := inclusion (le_sup_right : F.H ≤ K) c.rechoice
  let k : K := c.gammaConjugator*r
  let w := k⁻¹ • base Ω true
  have hb := c.three_le
  have hd : (graph Ω).dist w (base Ω false) ≤ c.b-2 := by
    have hh := SimpleGraph.dist_le (c.path.drop 2)
    rw [SimpleGraph.Walk.drop_length,c.length] at hh
    have hw : w = r⁻¹ • (c.gammaConjugator⁻¹ • base Ω true) := by
      simp only [w,k,mul_inv_rev,mul_smul]
    rw [hw,←c.alignment,CosetGeometry.RankTwo.dist_smul,SimpleGraph.dist_comm]
    exact hh
  have hle := ChapterF.Section07.Track.ballKernel_le_of_dist_add_le Ω
    (ChapterF.Section07.Geometry.family_generates _ _) (m:=1) (n:=c.b-1)
    (show (graph Ω).dist w (base Ω false)+1 ≤ c.b-1 by omega)
  intro x hx
  obtain ⟨u,hu,he⟩ := hx
  obtain ⟨u',hu',hu'e⟩ := span_ballKernel h c hu
  have hk : k⁻¹*u'*k ∈ ballKernel Ω w (c.b-1) := by
    simpa only [inv_inv] using (conj_mem_ballKernel_iff Ω k⁻¹ u' (base Ω true) (c.b-1)).mpr hu'
  have hQ := base_kernel_le_Q_at h structural
    (mem_map_of_mem K.subtype (hle hk))
  have heq : K.subtype (k⁻¹*u'*k) = x := by
    rw [←he]
    change (c.conjugator)⁻¹ * (u':G) * c.conjugator =
      (MulAut.conj c.conjugator⁻¹) u
    rw [←hu'e]
    simp
  exact heq ▸ hQ

theorem critical_le_Ri_at (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) : c.Uα ≤ F.Ri L 1 := by
  have hQT : Q T L ≤ (T:Subgroup G) :=
    (pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  have hle : F.Li L 1 ⊔ (T:Subgroup G) ≤ L ⊔ (T:Subgroup G) :=
    sup_le_sup ((F.Li_le L 1).trans inf_le_left) le_rfl
  exact (critical_le_Q_at h structural c).trans
    ((le_inf (hQT.trans le_sup_right) le_rfl).trans (inf_pCoreIn_le_of_le 2 hle))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
