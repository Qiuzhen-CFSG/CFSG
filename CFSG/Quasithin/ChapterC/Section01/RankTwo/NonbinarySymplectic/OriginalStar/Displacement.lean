module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.FirstStar
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.CoreDisplacement
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.CoreDisplacement

/-!
# Displacement of the original star by the full core

The original critical path can be chosen through the marked holomorph vertex.
The edge-radius bound makes its star centralize the far endpoint. The first
star comparison, exact local generation and coprime commutator identities
then put the star's displacement by the entire core inside the full fixed
factor. No minimum replacement or vanishing fixed factor is used.

The internal import reuses local commutator lemmas from the same source family.
Source: MS93 (3.4), printed pp.868--869.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open MSCentralOrbit
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

/-- The complete characteristic star lies in each original-color core within
critical edge radius of the fixed holomorph vertex. -/
theorem Input.original_starSpan_le_core_of_distance
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (Y : Subgroup R) (P : Sylow 2 (Ltilde R (alpha R)))
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤
      normalizer (Y.map (embedS R) : Set (FreeAmalgam R)))
    {c : Vertex R} (hc : color R c = false)
    (hdist : (cosetGraph R).dist (beta R) c < geometry.b R) :
    (starSpan R Y).map (embedS R) ≤ Q R c := by
  have hbeta : (starSpan R Y).map (embedS R) =
      (⨆ k : Hbar R, (Y.map (embedS R)).map
        (MulAut.conj (k : FreeAmalgam R)).toMonoidHom) ⊔ Z R (beta R) := by
    simpa only [map_map,embedM_comp_subtype] using starSpan_map_graph R Y
  have hZc : Z R c ≤ Q R (beta R) :=
    Z_le_Q_of_dist_lt R c (geometry.exists_critical c hc) (by
      rw [geometry.distance_constant c hc,SimpleGraph.dist_comm]
      exact hdist)
  rw [hbeta]
  apply sup_le
  · apply iSup_le
    intro k
    obtain ⟨P',hP'⟩ := exists_componentSylowSeed_act R (alpha R) P
      (k : FreeAmalgam R)⁻¹
    simp only [inv_inv] at hP'
    have hk : (k : FreeAmalgam R) ∈ stabilizer R (beta R) := by
      simpa only [beta,stabilizer_h_base] using k.property
    have hkb : act R (k : FreeAmalgam R)⁻¹ (beta R) = beta R :=
      (stabilizer R (beta R)).inv_mem hk
    have hn' := map_seed_normalized_at_act R _ hn (k : FreeAmalgam R)⁻¹
    simp only [hkb,inv_inv] at hn'
    obtain ⟨_,hut⟩ := transported_seed_edges R 1 k
    simp only [OneMemClass.coe_one,inv_one,act_one] at hut
    rw [hY,←hP'] at hn' ⊢
    have hu : color R (act R (k : FreeAmalgam R)⁻¹ (alpha R)) = false := by
      rw [action_preserves_color]
      rfl
    have hu1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hut)
    have htri := (cosetGraph_connected R).dist_triangle
      (u := act R (k : FreeAmalgam R)⁻¹ (alpha R))
      (v := beta R) (w := c)
    apply h.original_sylow_seed_le_core_of_distance geometry hb hu hc
      (by omega) (by rwa [SimpleGraph.dist_comm]) P' hn'
  · rw [←C_eq_Q R (h.radical.isPGroup) (h.radical.twoCore_le)
      (h.omegaOrbit_centralizer) c hc]
    apply le_inf
    · have hba : Z R (beta R) ≤ Z R (alpha R) :=
        adjacent_Z_le R rfl (base_adjacent R)
      apply hba.trans
      apply Z_le_stabilizer_of_dist_le (alpha R) (geometry.exists_critical _ rfl)
      rw [geometry.distance_constant _ rfl]
      change (cosetGraph R).dist (alpha R) c ≤ geometry.b R
      have hab : (cosetGraph R).dist (alpha R) (beta R) = 1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj R _ _).mpr (base_adjacent R))
      have htri := (cosetGraph_connected R).dist_triangle
        (u := alpha R) (v := beta R) (w := c)
      omega
    · apply le_centralizer_iff.mp
      apply hZc.trans
      apply le_centralizer_iff.mp
      intro z hz
      rw [Z,if_neg (by change ¬ true = false; decide)] at hz
      exact (mem_omegaCenter_iff.mp hz).2.2

omit h in
/-- A critical path can be chosen through the original marked edge. -/
theorem exists_original_critical_path_through_beta
    (geometry : Geometry R) (hb : 0 < geometry.b R) :
    ∃ z : Vertex R, ∃ path : CriticalPath R geometry (alpha R) z,
      path.walk.getVert 1 = beta R := by
  obtain ⟨z,⟨path⟩⟩ := CriticalPath.exists_from (R := R) (geometry := geometry)
    (a := alpha R) rfl
  have hlen : 0 < path.walk.length := by rwa [path.length_eq_b]
  have hav : Adjacent R (alpha R) (path.walk.getVert 1) := by
    have hh := path.walk.adj_getVert_succ (i := 0) hlen
    simpa only [SimpleGraph.Walk.getVert_zero,Nat.zero_add] using
      ((cosetGraph_adj R _ _).mp hh)
  obtain ⟨x,hx,hxv⟩ := stabilizer_transitive_neighbors R (alpha R)
    hav (base_adjacent R)
  have hxa : act R x (alpha R) = alpha R := hx
  have he : ∃ z : Vertex R,
      ∃ p : CriticalPath R geometry (act R x (alpha R)) z,
        p.walk.getVert 1 = beta R := by
    refine ⟨act R x z,path.act x,?_⟩
    change (actWalk R x path.walk).getVert 1 = beta R
    rw [actWalk_getVert,hxv]
    rfl
  exact Eq.mp (congrArg (fun a => ∃ z : Vertex R,
    ∃ p : CriticalPath R geometry a z,
      p.walk.getVert 1 = beta R) hxa) he

/-- Actual source application: a critical path through the marked holomorph
vertex is centralized by its complete characteristic star. -/
theorem Input.original_starSpan_centralizes_endpoint
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    {z : Vertex R} (path : CriticalPath R geometry (alpha R) z)
    (hfirst : path.walk.getVert 1 = beta R)
    (Y : Subgroup R) (P : Sylow 2 (Ltilde R (alpha R)))
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤
      normalizer (Y.map (embedS R) : Set (FreeAmalgam R))) :
    (starSpan R Y).map (embedS R) ≤
      centralizer (Z R z : Set (FreeAmalgam R)) := by
  have hdist : (cosetGraph R).dist (beta R) z < geometry.b R := by
    rw [←hfirst,path.dist_end,path.length_eq_b]
    omega
  exact (h.original_starSpan_le_core_of_distance geometry hb Y P hY hn path.end_color hdist).trans
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q R z path.end_color)))



theorem Input.original_sourceStarAlpha_core_displacement
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    {z : Vertex R} (path : CriticalPath R geometry (alpha R) z)
    (hfirst : path.walk.getVert 1 = beta R)
    (Y : Subgroup R) (P : Sylow 2 (Ltilde R (alpha R)))
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤
      normalizer (Y.map (embedS R) : Set (FreeAmalgam R))) :
    ⁅sourceStarAlpha R Y,Q R (alpha R)⁆ ≤
      fixedCore R (alpha R) := by
  let S := stabilizer R (alpha R)
  let A := sourceStarAlpha R Y
  let B := (starSpan R Y).map (embedS R)
  let Q₀ := Q R (alpha R)
  let T := Q R (beta R)
  let J := Z R z
  have hAS : A ≤ S := sourceStarAlpha_le_stabilizer _ _
  have hBA : B ≤ A := by
    have hh := (sourceStarAlpha_le_iff R Y A).mp le_rfl (1 : Mbar R)
    have he : (MulAut.conj (1 : FreeAmalgam R)).toMonoidHom =
        MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      change 1 * x * 1⁻¹ = x
      simp
    simpa only [OneMemClass.coe_one,he,Subgroup.map_id] using hh
  have hBS := hBA.trans hAS
  have hQS : Q₀ ≤ S := fun _ hx => hx.1
  have hTS : T ≤ S := fun _ hx => hx.2 _ (adjacent_symm _ (base_adjacent _))
  have hQT : Q₀ ≤ T := Q_le_adjacent_h R rfl (base_adjacent _)
  have hJS : J ≤ S := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant _ rfl,
      geometry.distance_constant _ path.end_color]
  have hgen₀ : pResidual 2 H ⊔ R = ⊤ := by
    rw [h.residual_eq]
    apply top_unique
    intro x _
    obtain ⟨k,hk,r,hr,rfl⟩ := h.product x
    exact mul_mem (mem_sup_left hk) (mem_sup_right hr)
  have hgen : Ltilde R (alpha R) ⊔ T = S :=
    local_residual_edge_generation _ hgen₀ rfl (base_adjacent _)
  have hBn : T ≤ normalizer (B : Set (FreeAmalgam R)) := by
    rw [show T = R.map (embedM R) from Q_beta _]
    change R.map (embedM R) ≤ normalizer
      ((starSpan R Y).map (embedS R) : Set _)
    rw [←embedM_comp_subtype,←map_map]
    have hdn : R ≤ normalizer
        ((starSpan R Y).map R.subtype : Set H) := by
      have hh := le_normalizer_map (H := starSpan R Y) R.subtype
      rw [normalizer_eq_top_iff.mpr inferInstance,←MonoidHom.range_eq_map,range_subtype] at hh
      exact hh
    exact (map_mono hdn).trans (le_normalizer_map (embedM R))
  have htriple : ⁅⁅A,Ltilde R (alpha R)⁆,Q₀⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (commutator_mono
      (h.original_sourceStarAlpha_commutator_le_U geometry hb Y P hY hn) le_rfl).trans
      ((commutator_mono (U_le_Z _) le_rfl).trans (Z_centralizes_Q _ _ rfl).le)
  have hBJ : B ≤ centralizer (J : Set (FreeAmalgam R)) :=
    h.original_starSpan_centralizes_endpoint geometry hb path hfirst Y P hY hn
  let q := QuotientGroup.mk' (pCore 2 H)
  have hs := h.component_image_structure
  let : ((pResidual 2 H).map q).Normal := by rw [h.residual_eq]; exact hs.2.1
  let : IsSimpleGroup ((pResidual 2 H).map q) := by rw [h.residual_eq]; exact hs.2.2.1
  let : IsQuasisimple ((pResidual 2 H).map q) := by rw [h.residual_eq]; exact hs.2.2.2.1
  have hcent : centralizer ((pResidual 2 H).map q : Set (H ⧸ pCore 2 H)) = ⊥ := by
    rw [h.residual_eq]
    exact hs.2.2.2.2
  have hnot : ¬ J ≤ Q₀ := by
    have hedge := MSCentralOrbit.edgeCentralizerCondition R (h.radical.isPGroup)
      (h.radical.twoCore_le) (h.omegaOrbit_centralizer)
    exact (critical_reverse R geometry hedge _ rfl
      (by rwa [geometry.distance_constant _ rfl]) z path.end_color path.critical).2
  have hJgen := edge_conjugate_generation_of_centric_component R
    (h.radical.isPGroup) (h.radical.twoCore_le) hgen₀ q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hcent rfl
    (base_adjacent _) J hJS hnot
  change conjugatesIn J S ⊔ T = S at hJgen
  let : Finite S := finite_stabilizer _ _
  let : (Q₀.subgroupOf S).Normal := Q_normal _ _
  have hAc : A.subgroupOf S ≤ normalClosure (B.subgroupOf S : Set S) := by
    apply (map_le_map_iff_of_injective S.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hAS]
    apply (sourceStarAlpha_le_iff R Y _).mpr
    intro g
    rintro _ ⟨b,hb,rfl⟩
    have hg : (g : FreeAmalgam R) ∈ S := by
      simpa only [S,alpha,stabilizer_m_base] using g.property
    exact mem_map_of_mem S.subtype
      ((inferInstance : (normalClosure (B.subgroupOf S : Set S)).Normal).conj_mem
        ⟨b,hBS hb⟩ (le_normalClosure hb) ⟨g,hg⟩)
  have hJn : normalClosure (J.subgroupOf S : Set S) ⊔ T.subgroupOf S = ⊤ := by
    apply (map_injective S.subtype_injective)
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,map_subgroupOf_eq_of_le hTS]
    apply le_antisymm (sup_le (map_subtype_le _) hTS)
    exact hJgen.ge.trans (sup_le_sup_right (conjugatesIn_le_mapped_normalClosure S J hJS) T)
  have hgn : pResidual 2 S ⊔ T.subgroupOf S = ⊤ := by
    apply map_injective S.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hTS,←MonoidHom.range_eq_map,range_subtype]
    exact hgen
  have htn : IsPGroup 2 (T.subgroupOf S) := by
    have ht : IsPGroup 2 T := by
      rw [show T = R.map (embedM R) from Q_beta _]
      exact (h.radical.isPGroup).map _
    exact ht.comap_subtype
  have htri : ⁅⁅A.subgroupOf S,pResidual 2 S⁆,Q₀.subgroupOf S⁆ = ⊥ := by
    apply map_injective S.subtype_injective
    rw [map_commutator,map_commutator,map_subgroupOf_eq_of_le hAS,
      map_subgroupOf_eq_of_le hQS,Subgroup.map_bot]
    exact htriple
  have hbjn : B.subgroupOf S ≤ centralizer (J.subgroupOf S : Set S) := by
    intro b hb j hj
    exact Subtype.ext (hBJ hb j.val hj)
  have hbn : T.subgroupOf S ≤ normalizer (B.subgroupOf S : Set S) :=
    (comap_mono hBn).trans (le_normalizer_comap S.subtype)
  have hbound := seed_core_displacement (A.subgroupOf S) (B.subgroupOf S)
    (Q₀.subgroupOf S) (T.subgroupOf S) (J.subgroupOf S)
    (comap_mono hBA) hAc (comap_mono hQT) htn hgn hbn htri hbjn hJn
  have hh := map_mono (f := S.subtype) hbound
  rw [map_commutator,map_subgroupOf_eq_of_le hAS,map_subgroupOf_eq_of_le hQS] at hh
  intro x hx
  obtain ⟨y,hy,rfl⟩ := hh hx
  refine ⟨hy.1,?_⟩
  rintro _ ⟨l,hl,rfl⟩
  exact congrArg Subtype.val (hy.2 l hl)

/-- In particular the full characteristic holomorph star has the displacement
required by the centralizer cut, before its moving-plus-fixed inclusion. -/
theorem Input.original_starSpan_core_displacement
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (Y : Subgroup R) (P : Sylow 2 (Ltilde R (alpha R)))
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤
      normalizer (Y.map (embedS R) : Set (FreeAmalgam R))) :
    ⁅(starSpan R Y).map (embedS R),Q R (alpha R)⁆ ≤
      fixedCore R (alpha R) := by
  obtain ⟨z,path,hfirst⟩ := exists_original_critical_path_through_beta geometry hb
  have hB : (starSpan R Y).map (embedS R) ≤ sourceStarAlpha R Y := by
    have hh := (sourceStarAlpha_le_iff R Y (sourceStarAlpha R Y)).mp
      le_rfl (1 : Mbar R)
    have he : (MulAut.conj (1 : FreeAmalgam R)).toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      change 1 * x * 1⁻¹ = x
      simp
    simpa only [OneMemClass.coe_one,he,Subgroup.map_id] using hh
  exact (commutator_mono hB le_rfl).trans
    (h.original_sourceStarAlpha_core_displacement geometry hb path hfirst Y P hY hn)


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
