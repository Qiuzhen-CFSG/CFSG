module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Paths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Consequences.Geometry

/-!
# Containment and nontriviality in the first path intersection

The radius group splits into its moving subgroup and an incident odd-color
radius. Distance makes that second factor centralize the opposite radius.
The remaining commutator lies in H at each endpoint. A neighboring critical
window supplies noncommuting Z-layers in the two radii, so their commutator
is nontrivial. This also proves H_a nontrivial for every M-vertex.

These are the containment and nontriviality steps of (4.5.1)(i), not its
reverse inclusion or exact order. Only local groups are finite; the free
amalgam and its tree remain infinite.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.1)(i), printed p.896.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early
open PathCentrality PathCentrality.RegularPaths
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}
  {source : LocalSource L R}

private theorem H_normalized (a : Vertex R) :
    stabilizer R a ≤ normalizer (H R a : Set (FreeAmalgam R))  := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (⁅Vcirc R a, Q R a⁆ : Subgroup (FreeAmalgam R)).map _ = _
  rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (Vcirc_normalized a hg),
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized R a hg)]
  rfl

/-- The odd-color radius near the first endpoint centralizes the opposite radius. -/
theorem edgeRadius_centralizes_radius {a t d : Vertex R}
    (ha : color R a = false) (hat : Adjacent R a t) (hd : color R d = false)
    (htd : (cosetGraph R).dist t d + 3 < geometry.b R) :
    ⁅V R t, V R d⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply Escape.Initial.Consequences.V_le_of_h_neighbors ha hat
  intro u hut
  have hu : color R u = false := by
    have hat' := adjacent_color_ne R hat
    have hut' := adjacent_color_ne R hut
    cases h : color R u <;> cases h' : color R t <;> simp_all
  have hVu : V R d ≤ Q R u := by
    apply V_le_Q_of_dist_add_two_lt R hd
    have hud := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hut)
    have htri := (cosetGraph_connected R).dist_triangle (u := u) (v := t) (w := d)
    rw [SimpleGraph.dist_comm (u := d) (v := u)]
    omega
  exact (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes u hu)).trans
    (centralizer_le hVu)

/-- The first half of (4.5.1)(i) follows from moving/edge generation and distance. -/
theorem radius_commutator_le_H [Finite M] (source : LocalSource L R)
    (earlier : Earlier R geometry) {a d : Vertex R}
    (ha : color R a = false) (hd : color R d = false)
    (had : (cosetGraph R).dist a d = 4) : ⁅V R a, V R d⁆ ≤ H R a := by
  obtain ⟨w, hw⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist a d
  have hw4 : w.length = 4 := hw.trans had
  have hat : Adjacent R a (w.getVert 1) := by
    have hh := w.adj_getVert_succ (i := 0) (by omega)
    simpa only [SimpleGraph.Walk.getVert_zero] using (cosetGraph_adj R _ _).mp hh
  have htd : (cosetGraph R).dist (w.getVert 1) d = 3 := by
    have hh := SimpleGraph.length_eq_dist_of_subwalk hw (w.isSubwalk_drop 1)
    simpa only [SimpleGraph.Walk.drop_length, hw4] using hh.symm
  have hedge := edgeRadius_centralizes_radius ha hat hd
    (by rw [htd, earlier.distance]; decide)
  have hVQ : V R a ≤ Q R a := V_le_Q R ha (by rw [earlier.distance]; decide)
  have hDQ : V R d ≤ Q R a := V_le_Q_of_dist_add_two_lt R hd
    (by rw [SimpleGraph.dist_comm, had, earlier.distance]; decide)
  have hpre : V R a ≤ commutatorPreimage (Q R a) (V R d) (H R a) := by
    rw [Escape.Initial.Consequences.radius_eq_moving_sup_edge source ha hat]
    exact sup_le
      (le_commutatorPreimage ((DistanceEight.Vcirc_le_V R a).trans hVQ)
        (commutator_mono le_rfl hDQ))
      (le_commutatorPreimage ((Escape.Initial.Consequences.edge_radius_le_radius ha hat).trans hVQ)
        (hedge.le.trans bot_le))
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _
      ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans (H_normalized a)))

/-- Both symmetric containments in (4.5.1)(i), on the literal radius subgroups. -/
theorem radius_commutator_le_intersection [Finite M] (source : LocalSource L R)
    (earlier : Earlier R geometry) {a d : Vertex R}
    (ha : color R a = false) (hd : color R d = false)
    (had : (cosetGraph R).dist a d = 4) :
    ⁅V R a, V R d⁆ ≤ H R a ⊓ H R d := by
  refine le_inf (radius_commutator_le_H source earlier ha hd had) ?_
  rw [commutator_comm]
  exact radius_commutator_le_H source earlier hd ha (by rw [SimpleGraph.dist_comm]; exact had)

/-- The neighboring critical window witnesses nontriviality of the radius commutator. -/
theorem path_commutator_ne_bot (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (e : ExtendedPath geometry a)
    {i : ℕ} (hi : Even i) (hi2 : 2 ≤ i) (hi10 : i ≤ 10) :
    ⁅V R (e.walk.getVert i), V R (e.walk.getVert (i + 4))⁆ ≠ ⊥ := by
  have he : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
  let p := e.window (i - 2) he (by omega)
  have hnon := common.critical_noncommutation _ p.start_color _ p.critical
  have hlen : e.walk.length = 16 := by rw [e.length_eq, earlier.distance]
  have hend : i - 2 + geometry.b R = i + 6 := by rw [earlier.distance]; omega
  change ⁅Z R (e.walk.getVert (i - 2)), Z R (e.walk.getVert (i - 2 + geometry.b R))⁆ ≠ ⊥ at hnon
  rw [hend] at hnon
  have hleft : Z R (e.walk.getVert (i - 2)) ≤ V R (e.walk.getVert i) :=
    le_iSup_of_le _ (le_iSup_of_le
      (by rw [segment_distance e (by omega) (by omega)]; omega) le_rfl)
  have hright : Z R (e.walk.getVert (i + 6)) ≤ V R (e.walk.getVert (i + 4)) :=
    le_iSup_of_le _ (le_iSup_of_le
      (by rw [SimpleGraph.dist_comm, segment_distance e (by omega) (by omega)]; omega) le_rfl)
  intro hz
  exact hnon (le_bot_iff.mp ((commutator_mono hleft hright).trans hz.le))

/-- The preceding critical configuration already forces the actual fixed commutator nontrivial. -/
theorem H_ne_bot [Finite M] (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (ha : color R a = false) : H R a ≠ ⊥ := by
  obtain ⟨e⟩ := earlier.extended a ha
  have hlen : e.walk.length = 16 := by rw [e.length_eq, earlier.distance]
  have hn := path_commutator_ne_bot common earlier e (i := 4) (by decide) (by omega) (by omega)
  have hh := radius_commutator_le_intersection source earlier
    (path_color e (i := 4) (by decide) (by omega))
    (path_color e (i := 8) (by decide) (by omega))
    (show (cosetGraph R).dist (e.walk.getVert 4) (e.walk.getVert 8) = 4 by
      rw [segment_distance e (by omega) (by omega)])
  rw [e.center_eq] at hn hh
  exact fun h => hn (le_bot_iff.mp ((hh.trans inf_le_left).trans h.le))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early
