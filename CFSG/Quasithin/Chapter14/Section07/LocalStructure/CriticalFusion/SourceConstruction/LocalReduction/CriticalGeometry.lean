module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingBranch
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.F8SourceApplication
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourcePath

/-!
# Critical geometry before the local module recognition

The original natural L₃(2) action and abelian H-span supply the F.8
hypotheses. Its shortest critical path and local transitivity construct the
literal `CriticalPath`, including the permitted H-rechoice. In the alternating
residual branch, the proved S₅ quotient supplies escape, so no recognition
datum or separate escape premise is needed.

Ball-kernel containment places the conjugate span Uα in Q = O₂(LT), and
restriction gives Uα ≤ R₁. The two-core of H fixes its first neighborhood;
criticality therefore forces U/(U ∩ Qα) to be nontrivial. The final application
constructs this geometry on the original flag before natural recognition.
These arguments adapt the existing Data-based CriticalSelection, ReciprocalEven
and ActorPlacement proofs, retaining their literal graph and conjugation maps.

The rank comparison between this index and |Uα*|, the natural-module upper
bound and the residual classification remain source obligations. This module
proves their geometric preparation, not 14.7.40 or 14.7.52.

Source: Aschbacher–Smith, F.8.4–5 and F.9.13–14, printed pp.316–317,322–323;
14.5.18 and Notation 14.7.1, printed pp.1018,1042–1043.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Original F8 hypotheses on the actual LT/H pair. -/
theorem f8_hypothesis (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (structural:Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness:Uniqueness127 KnownSimple.IsKnownSimple.{u}) :
    ChapterF.Section08.Setup.Hypothesis (F.f8SourceSetup L F.H) := by
  let := h.chosen.elementary
  obtain ⟨z, hz, he⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hJ := F.H_mem_Hz (by decide) L (normalizer (L : Set G)) hescape
  have hzV : z ∈ V := F.le_seed 1 (he.symm ▸ mem_zpowers z)
  apply F.f8Source_hypothesis h.source.simpleQTKE L (normalizer (L:Set G))
    (by decide) h.chosen.le_sylow h.chosen.normalizes
    (h.sylow_normalizes structural) h.residual
    (fun _=>⟨h.naturalMarking⟩) rfl
    (h.maximal_unique structural uniqueness).2
    (h.seed_centralizer_le structural uniqueness) h.centralizer_L
    h.source.maximal_faithful.2.1.2.2 (h.seed_reduced structural)
    (h.centralizer_LT structural) z he hz _ hab F.H hJ
  intro x hx hx1
  obtain ⟨l,hl,he⟩ := h.vector_transitive hzV hx hz hx1
  exact ⟨l,h.chosen.normalizes hl,he⟩

open Subgroup.CosetGeometry.RankTwo

set_option backward.isDefEq.respectTransparency false in
/-- First critical path and the actual H adjustment. -/
theorem exists_criticalPath (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (structural:Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness:Uniqueness127 KnownSimple.IsKnownSimple.{u}) :
    Nonempty (CriticalPath (L:=L) F) := by
  classical
  let D:=F.f8SourceSetup L F.H
  let hf:ChapterF.Section08.Setup.Hypothesis D:=f8_hypothesis h hab hescape structural uniqueness
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

/-- The alternating residual branch supplies escape before natural recognition. -/
theorem exists_criticalPath_of_alternating
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hAlt : AlternatingResidual F) : Nonempty (CriticalPath (L := L) F) := by
  obtain ⟨e⟩ := exists_symmetric_star h structural hAlt
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S B hB
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hB
  exact exists_criticalPath h hab (alternating_escape h hab structural e) structural uniqueness

/-- The actual orbit span fixes the full ball about the first H vertex. -/
theorem span_ballKernel (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) (c : CriticalPath (L := L) F) :
    F.U ≤ (ballKernel (geometryFamily (L := L) F)
      (base (geometryFamily (L := L) F) true) (c.b-1)).map (GeometryGroup T L F).subtype := by
  let K := GeometryGroup T L F
  let Ω := geometryFamily (L := L) F
  let B := ballKernel Ω (base Ω true) (c.b-1)
  have hV : V ≤ B.map K.subtype := by
    intro v hv
    have hvK : v ∈ K := ((le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G)).trans le_sup_left)
      (h.chosen.le_sylow hv)
    refine ⟨⟨v,hvK⟩,?_,rfl⟩
    have h := (c.radius c.b).mpr le_rfl (show (⟨v,hvK⟩ : K) ∈ V.subgroupOf K from hv)
    have hn := ballKernel_succ_le Ω
      (show (graph Ω).Adj (base Ω false) (base Ω true) from
        ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base Ω false true⟩) (c.b-1)
    apply hn
    simpa only [Nat.sub_add_cancel (by have := c.three_le; omega : 1 ≤ c.b)] using h
  have hH : F.H ≤ normalizer (B.map K.subtype : Set G) := by
    intro h hh
    have hhK : h ∈ K := (le_sup_right : F.H ≤ K) hh
    have hn : (⟨h,hhK⟩ : K) ∈ normalizer (B : Set K) := by
      apply stabilizer_le_normalizer_ballKernel Ω (base Ω true) (c.b-1)
      change (⟨h,hhK⟩ : K) ∈ stabilizer Ω (base Ω true)
      simpa only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base] using
        (show (⟨h,hhK⟩ : K) ∈ Ω true from hh)
    exact le_normalizer_map K.subtype ⟨⟨h,hhK⟩,hn,rfl⟩
  exact conjugateSpanBy_le hV hH

/-- The first neighborhood detects the natural action on V. -/
theorem base_kernel_le_Q (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
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
  rw [← h.centralizer_LT structural]
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


/-- The stronger placement in the literal two-core Q. -/
theorem critical_le_Q (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
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
  have hQ := base_kernel_le_Q h structural
    (mem_map_of_mem K.subtype (hle hk))
  have heq : K.subtype (k⁻¹*u'*k) = x := by
    rw [←he]
    change (c.conjugator)⁻¹ * (u':G) * c.conjugator =
      (MulAut.conj c.conjugator⁻¹) u
    rw [←hu'e]
    simp
  exact heq ▸ hQ

/-- The source R₁ placement follows by restricting the original two-core. -/
theorem critical_le_Ri (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) : c.Uα ≤ F.Ri L 1 := by
  have hQT : Q T L ≤ (T:Subgroup G) :=
    (pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  have hle : F.Li L 1 ⊔ (T:Subgroup G) ≤ L ⊔ (T:Subgroup G) :=
    sup_le_sup ((F.Li_le L 1).trans inf_le_left) le_rfl
  exact (critical_le_Q h structural c).trans
    ((le_inf (hQT.trans le_sup_right) le_rfl).trans (inf_pCoreIn_le_of_le 2 hle))

omit [Finite G] in
/-- The literal two-core fixes the first H-neighborhood. -/
theorem core_le_H_neighborhood :
    F.H.pCoreIn 2 ≤ (ballKernel (geometryFamily (L:=L) F)
      (base (geometryFamily (L:=L) F) true) 1).map (GeometryGroup T L F).subtype := by
  let X := GeometryGroup T L F
  let Ω := geometryFamily (L:=L) F
  have hQT : F.H.pCoreIn 2 ≤ (T:Subgroup G) :=
    (pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))).trans_eq
      (map_subgroupOf_eq_of_le (F.invariant 1))
  have hn : F.H ≤ normalizer (F.H.pCoreIn 2 : Set G) :=
    F.H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))
  intro q hq
  let q' : X := ⟨q,mem_sup_right (pCoreIn_le 2 F.H hq)⟩
  refine ⟨q',?_,rfl⟩
  intro w hw
  rcases (mem_ball_one Ω (base Ω true) w).mp hw with hw | rfl
  · obtain ⟨h,hh,rfl⟩ := locally_transitive Ω
      (show (graph Ω).Adj (base Ω true) (base Ω false) from
        ⟨by change true≠false; decide,CosetGeometry.incident_base Ω true false⟩) hw
    have hhH : (h:G) ∈ F.H := by
      have hh' : h ∈ Ω true := by
        simpa only [stabilizer,base,CosetGeometry.stabilizer_base] using hh
      exact hh'
    have hc : (h:G)⁻¹*q*(h:G) ∈ F.H.pCoreIn 2 := by
      simpa only [inv_inv] using
        (mem_normalizer_iff.mp (hn (F.H.inv_mem hhH)) q).mp hq
    have hm : h⁻¹*q'*h ∈ Ω false := mem_sup_right (hQT hc)
    have hf : (h⁻¹*q'*h) • base Ω false=base Ω false := by
      apply MulAction.mem_stabilizer_iff.mp
      simpa only [CosetGeometry.stabilizer_base] using hm
    calc
      q' • (h • base Ω false) = h • ((h⁻¹*q'*h) • base Ω false) := by
        simp only [mul_smul,smul_inv_smul]
      _ = h • base Ω false := congrArg (h • ·) hf
  · apply MulAction.mem_stabilizer_iff.mp
    simpa only [CosetGeometry.stabilizer_base] using
      (show q' ∈ Ω true from pCoreIn_le 2 F.H hq)

omit [Finite G] in
/-- Criticality excludes containment in the reciprocal point core. -/
theorem critical_span_not_le_reciprocal_core (c : CriticalPath (L:=L) F) :
    ¬ F.U ≤ c.Qα := by
  intro hU
  let X := GeometryGroup T L F
  let Ω := geometryFamily (L:=L) F
  apply c.critical
  intro v hv
  have hvU : (v:G) ∈ F.U := (le_conjugateSpanBy V F.H) hv
  have hvh : (c.rechoice:G)⁻¹*(v:G)*(c.rechoice:G) ∈ F.U := by
    have hn : (c.rechoice:G) ∈ normalizer (F.U : Set G) :=
      le_normalizer_conjugateSpanBy V F.H c.rechoice.property
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp ((normalizer (F.U : Set G)).inv_mem hn) (v:G)).mp hvU
  have hq := hU hvh
  change (c.rechoice:G)⁻¹*(v:G)*(c.rechoice:G) ∈
    (conjugate F.H c.conjugator).pCoreIn 2 at hq
  unfold conjugate at hq
  rw [← map_pCoreIn_of_injective 2 F.H (MulAut.conj c.conjugator⁻¹).toMonoidHom
    (MulAut.conj c.conjugator⁻¹).injective] at hq
  obtain ⟨q,hq,he⟩ := hq
  have heq : (c.gammaConjugator:G)*(v:G)*(c.gammaConjugator:G)⁻¹=q := by
    simp only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv] at he
    have he' := congrArg (fun x:G => c.conjugator*x*c.conjugator⁻¹) he
    simp only [CriticalPath.conjugator,mul_inv_rev] at he'
    group at he'
    simpa only [zpow_neg_one] using he'.symm
  have hq' := (core_le_H_neighborhood (L:=L) (F:=F)) hq
  obtain ⟨q',hq',he'⟩ := hq'
  have hval : c.gammaConjugator*v*c.gammaConjugator⁻¹=q' :=
    Subtype.ext (heq.trans he'.symm)
  apply (conj_mem_ballKernel_iff Ω c.gammaConjugator v
    (c.gammaConjugator⁻¹ • base Ω true) 1).mp
  rw [smul_inv_smul,hval]
  exact hq'

/-- The source reciprocal core index has positive binary logarithm. -/
theorem critical_index_positive (c : CriticalPath (L:=L) F) :
    0 < Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) := by
  have hn : (F.U ⊓ c.Qα).relIndex F.U ≠ 1 := by
    intro he
    exact critical_span_not_le_reciprocal_core c ((relIndex_eq_one.mp he).trans inf_le_right)
  have hp : 0 < (F.U ⊓ c.Qα).relIndex F.U := Nat.pos_of_ne_zero (by
    intro he
    have hh := relIndex_dvd_card (F.U ⊓ c.Qα) F.U
    rw [he,zero_dvd_iff] at hh
    exact Nat.card_pos.ne' hh)
  exact Nat.log_pos (by decide) (by omega)

/-- The alternating branch supplies a genuine critical path with its source
placement and a nontrivial reciprocal core index, before natural recognition. -/
theorem exists_critical_geometry_of_alternating
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hAlt : AlternatingResidual F) :
    ∃ c : CriticalPath (L := L) F,
      c.Uα ≤ F.Ri L 1 ∧
      F.U ≤ conjugate F.H c.conjugator ∧
      0 < Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) := by
  obtain ⟨c⟩ := exists_criticalPath_of_alternating h hab structural hAlt
  exact ⟨c, critical_le_Ri h structural c, G2Source.reciprocal_placement h c,
    critical_index_positive c⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
