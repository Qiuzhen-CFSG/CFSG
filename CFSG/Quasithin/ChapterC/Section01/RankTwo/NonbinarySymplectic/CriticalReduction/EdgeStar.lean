module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.FirstStar

/-!
# The holomorph star centralizes its critical endpoint

Transport each full-Sylow seed about the fixed holomorph vertex. Its distance
to an endpoint at edge radius less than b is at most b, and the critical-seed
lemma puts it in that endpoint's core. The central omega attachment also
lies in the exact endpoint centralizer. Thus the whole characteristic star
centralizes the critical endpoint on a path through its marked first edge.

Source: MS93 (3.4), printed pp.868--869.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The complete characteristic star lies in each original-color core within
critical edge radius of the fixed holomorph vertex. -/
theorem Input.replacement_starSpan_le_core_of_distance
    (geometry : Geometry d.radical) (hb : 0 < geometry.b d.radical)
    (Y : Subgroup d.radical) (P : Sylow 2 (Ltilde d.radical (alpha d.radical)))
    (hY : Y.map (embedS d.radical) = componentSylowSeed d.radical (alpha d.radical) P)
    (hn : Q d.radical (beta d.radical) ≤
      normalizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical)))
    {c : Vertex d.radical} (hc : color d.radical c = false)
    (hdist : (cosetGraph d.radical).dist (beta d.radical) c < geometry.b d.radical) :
    (starSpan d.radical Y).map (embedS d.radical) ≤ Q d.radical c := by
  have hbeta : (starSpan d.radical Y).map (embedS d.radical) =
      (⨆ k : Hbar d.radical, (Y.map (embedS d.radical)).map
        (MulAut.conj (k : FreeAmalgam d.radical)).toMonoidHom) ⊔ Z d.radical (beta d.radical) := by
    simpa only [map_map,embedM_comp_subtype] using starSpan_map_graph d.radical Y
  have hZc : Z d.radical c ≤ Q d.radical (beta d.radical) :=
    Z_le_Q_of_dist_lt d.radical c (geometry.exists_critical c hc) (by
      rw [geometry.distance_constant c hc,SimpleGraph.dist_comm]
      exact hdist)
  rw [hbeta]
  apply sup_le
  · apply iSup_le
    intro k
    obtain ⟨P',hP'⟩ := exists_componentSylowSeed_act d.radical (alpha d.radical) P
      (k : FreeAmalgam d.radical)⁻¹
    simp only [inv_inv] at hP'
    have hk : (k : FreeAmalgam d.radical) ∈ stabilizer d.radical (beta d.radical) := by
      simpa only [beta,stabilizer_h_base] using k.property
    have hkb : act d.radical (k : FreeAmalgam d.radical)⁻¹ (beta d.radical) = beta d.radical :=
      (stabilizer d.radical (beta d.radical)).inv_mem hk
    have hn' := map_seed_normalized_at_act d.radical _ hn (k : FreeAmalgam d.radical)⁻¹
    simp only [hkb,inv_inv] at hn'
    obtain ⟨_,hut⟩ := transported_seed_edges d.radical 1 k
    simp only [OneMemClass.coe_one,inv_one,act_one] at hut
    rw [hY,←hP'] at hn' ⊢
    have hu : color d.radical (act d.radical (k : FreeAmalgam d.radical)⁻¹ (alpha d.radical)) = false := by
      rw [action_preserves_color]
      rfl
    have hu1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hut)
    have htri := (cosetGraph_connected d.radical).dist_triangle
      (u := act d.radical (k : FreeAmalgam d.radical)⁻¹ (alpha d.radical))
      (v := beta d.radical) (w := c)
    apply h.replacement_sylow_seed_le_core_of_distance d geometry hb hu hc
      (by omega) (by rwa [SimpleGraph.dist_comm]) P' hn'
  · rw [←C_eq_Q d.radical (h.replacement_two_group d) (h.replacement_core_le d)
      (h.replacement_omegaOrbit_centralizer d) c hc]
    apply le_inf
    · have hba : Z d.radical (beta d.radical) ≤ Z d.radical (alpha d.radical) :=
        adjacent_Z_le d.radical rfl (base_adjacent d.radical)
      apply hba.trans
      apply Z_le_stabilizer_of_dist_le (alpha d.radical) (geometry.exists_critical _ rfl)
      rw [geometry.distance_constant _ rfl]
      change (cosetGraph d.radical).dist (alpha d.radical) c ≤ geometry.b d.radical
      have hab : (cosetGraph d.radical).dist (alpha d.radical) (beta d.radical) = 1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj d.radical _ _).mpr (base_adjacent d.radical))
      have htri := (cosetGraph_connected d.radical).dist_triangle
        (u := alpha d.radical) (v := beta d.radical) (w := c)
      omega
    · apply le_centralizer_iff.mp
      apply hZc.trans
      apply le_centralizer_iff.mp
      intro z hz
      rw [Z,if_neg (by change ¬ true = false; decide)] at hz
      exact (mem_omegaCenter_iff.mp hz).2.2

omit h in
/-- A critical path can be chosen through the original marked edge. -/
theorem exists_replacement_critical_path_through_beta
    (geometry : Geometry d.radical) (hb : 0 < geometry.b d.radical) :
    ∃ z : Vertex d.radical, ∃ path : CriticalPath d.radical geometry (alpha d.radical) z,
      path.walk.getVert 1 = beta d.radical := by
  obtain ⟨z,⟨path⟩⟩ := CriticalPath.exists_from (R := d.radical) (geometry := geometry)
    (a := alpha d.radical) rfl
  have hlen : 0 < path.walk.length := by rwa [path.length_eq_b]
  have hav : Adjacent d.radical (alpha d.radical) (path.walk.getVert 1) := by
    have hh := path.walk.adj_getVert_succ (i := 0) hlen
    simpa only [SimpleGraph.Walk.getVert_zero,Nat.zero_add] using
      ((cosetGraph_adj d.radical _ _).mp hh)
  obtain ⟨x,hx,hxv⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical)
    hav (base_adjacent d.radical)
  have hxa : act d.radical x (alpha d.radical) = alpha d.radical := hx
  have he : ∃ z : Vertex d.radical,
      ∃ p : CriticalPath d.radical geometry (act d.radical x (alpha d.radical)) z,
        p.walk.getVert 1 = beta d.radical := by
    refine ⟨act d.radical x z,path.act x,?_⟩
    change (actWalk d.radical x path.walk).getVert 1 = beta d.radical
    rw [actWalk_getVert,hxv]
    rfl
  exact Eq.mp (congrArg (fun a => ∃ z : Vertex d.radical,
    ∃ p : CriticalPath d.radical geometry a z,
      p.walk.getVert 1 = beta d.radical) hxa) he

/-- Actual source application: a critical path through the marked holomorph
vertex is centralized by its complete characteristic star. -/
theorem Input.replacement_starSpan_centralizes_endpoint
    (geometry : Geometry d.radical) (hb : 0 < geometry.b d.radical)
    {z : Vertex d.radical} (path : CriticalPath d.radical geometry (alpha d.radical) z)
    (hfirst : path.walk.getVert 1 = beta d.radical)
    (Y : Subgroup d.radical) (P : Sylow 2 (Ltilde d.radical (alpha d.radical)))
    (hY : Y.map (embedS d.radical) = componentSylowSeed d.radical (alpha d.radical) P)
    (hn : Q d.radical (beta d.radical) ≤
      normalizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical))) :
    (starSpan d.radical Y).map (embedS d.radical) ≤
      centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) := by
  have hdist : (cosetGraph d.radical).dist (beta d.radical) z < geometry.b d.radical := by
    rw [←hfirst,path.dist_end,path.length_eq_b]
    omega
  exact (h.replacement_starSpan_le_core_of_distance d geometry hb Y P hY hn path.end_color hdist).trans
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical z path.end_color)))

/-- The source first star comparison and endpoint centrality hold together
for an actual critical path on the replacement. -/
theorem Input.exists_replacement_star_comparisons
    (geometry : Geometry d.radical) (hb : 0 < geometry.b d.radical)
    (Y : Subgroup d.radical) (P : Sylow 2 (Ltilde d.radical (alpha d.radical)))
    (hY : Y.map (embedS d.radical) = componentSylowSeed d.radical (alpha d.radical) P)
    (hn : Q d.radical (beta d.radical) ≤
      normalizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical))) :
    ∃ z : Vertex d.radical, ∃ path : CriticalPath d.radical geometry (alpha d.radical) z,
      path.walk.getVert 1 = beta d.radical ∧
      ⁅sourceStarAlpha d.radical Y,Ltilde d.radical (alpha d.radical)⁆ ≤
        Z d.radical (alpha d.radical) ∧
      (starSpan d.radical Y).map (embedS d.radical) ≤
        centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) := by
  obtain ⟨z,path,hfirst⟩ := exists_replacement_critical_path_through_beta d geometry hb
  exact ⟨z,path,hfirst,h.replacement_sourceStarAlpha_commutator_le_Z d geometry hb Y P hY hn,
    h.replacement_starSpan_centralizes_endpoint d geometry hb path hfirst Y P hY hn⟩

/-- The intrinsic input constructs the actual seed, critical path and both
first-stage star comparisons on its characteristic replacement. -/
theorem Input.exists_replacement_first_star
    : ∃ geometry : Geometry d.radical, 0 < geometry.b d.radical ∧
      ∃ P : Sylow 2 (Ltilde d.radical (alpha d.radical)), ∃ Y : Subgroup d.radical,
      ∃ z : Vertex d.radical, ∃ path : CriticalPath d.radical geometry (alpha d.radical) z,
        Y.map (embedS d.radical) = componentSylowSeed d.radical (alpha d.radical) P ∧
        Q d.radical (beta d.radical) ≤
          normalizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical)) ∧
        path.walk.getVert 1 = beta d.radical ∧
        ⁅sourceStarAlpha d.radical Y,Ltilde d.radical (alpha d.radical)⁆ ≤
          U d.radical (alpha d.radical) ∧
        (starSpan d.radical Y).map (embedS d.radical) ≤ Q d.radical z := by
  obtain ⟨geometry,hb,_⟩ := h.replacement_positive_even_geometry d
  obtain ⟨P,Y,hY,hn,_,_⟩ := h.exists_replacement_source_seed d
  obtain ⟨z,path,hfirst⟩ := exists_replacement_critical_path_through_beta d geometry hb
  refine ⟨geometry,hb,P,Y,z,path,hY,hn,hfirst,
    h.replacement_sourceStarAlpha_commutator_le_U d geometry hb Y P hY hn,?_⟩
  apply h.replacement_starSpan_le_core_of_distance d geometry hb Y P hY hn path.end_color
  rw [←hfirst,path.dist_end,path.length_eq_b]
  omega

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
