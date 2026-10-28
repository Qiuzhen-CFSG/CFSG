module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Replacement.Path
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Neighbor

/-!
# The selected critical replacement in MS93 (4.5.4)(ii)

Apply the preceding (4.4.4) to the constructed regular path for (d^g,d).
The same local conjugator gives both a new endpoint r and an actual incident
neighbor. Its edge commutator is not normalized by Z_d, and (r,c) is critical.
Distance puts Z_a and Z_(c^g) into Q_r; reversed criticality therefore excludes
Z_c from their join. The preceding radius-commutator equality also puts
[Z_r,Z_c] in H_d, as required by the last sentence of p.898.

These are constructed geometric and commutator inputs to the two cases on
p.899. They do not prove the selected neighbor's Z-inequality, its subsequent
local normalizer bound, or the equal-edge Z comparison. In particular, this
module does not assert (4.5.4)(ii). No later marked quotient or core conclusion
is used. The extra radius-commutator premise is exactly (4.5.1)(i), produced
by qt-c01-ms93-core-factors-early-layers and discharged by the outer assembly.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.4), p.894,
and (4.5.4)(ii), pp.898--899.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Replacement
open PathCentrality
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

/-- The actual replacement from (4.4.4). The retained neighbor is the image
of the original first edge under the same conjugator as the new endpoint.
Its nonnormalization and criticality are proved by `exists_witness`. -/
structure Witness {a : Vertex R} (p : Higher.SourcePath a) (g : stabilizer R a) where
  conjugator : FreeAmalgam R
  conjugator_local : conjugator ∈ stabilizer R (act R g (p.walk.getVert 8))
  neighbor : Vertex R
  neighbor_eq : neighbor = act R conjugator (act R g (p.walk.getVert 7))
  first_adjacent : Adjacent R (act R g (p.walk.getVert 8)) neighbor
  second_adjacent : Adjacent R (act R conjugator (act R g (p.walk.getVert 6))) neighbor
  nonnormalization : ¬ Z R (p.walk.getVert 8) ≤
    stabilizer R (act R g (p.walk.getVert 8)) ⊓
      normalizer (edgeCommutator R (act R g (p.walk.getVert 8)) neighbor : Set (FreeAmalgam R))
  critical_distance : (cosetGraph R).dist
    (act R conjugator (act R g (p.walk.getVert 6))) (p.walk.getVert 6) = 8
  critical_noncontainment : ¬ Z R (act R conjugator (act R g (p.walk.getVert 6))) ≤
    Q R (p.walk.getVert 6)

/-- Apply Earlier.replacement to the explicit regular orbit path. An incident
nonnormalizing edge exists by the genuine natural action. Transporting its
commutator equality retains an adjacent neighbor for the selected endpoint. -/
theorem exists_witness [Finite M] {source : LocalSource L R}
    (common : CommonFacts R source geometry) {a : Vertex R} (p : Higher.SourcePath a)
    (earlier : Earlier R geometry) (g : stabilizer R a)
    (hd : (cosetGraph R).dist (act R g (p.walk.getVert 8)) (p.walk.getVert 8) = 8)
    (hn : ¬ Z R (act R g (p.walk.getVert 8)) ≤ Q R (p.walk.getVert 8)) :
    Nonempty (Witness p g) := by
  let q := orbitCriticalPath p earlier g hd hn
  obtain ⟨t, ht, hnt⟩ := RegularPaths.CommutatorPropagation.exists_nonnormalizing_neighbor common q
  obtain ⟨h, hh, he, hnc⟩ := earlier.replacement _ _ q
    (orbitCriticalPath_regular p earlier g hd hn) t ht hnt
  let r := q.conjugateShift (by rw [earlier.distance]; decide) h hh hnc
  have hfix : act R h (act R g (p.walk.getVert 8)) = act R g (p.walk.getVert 8) := hh
  have hedge : edgeCommutator R (act R g (p.walk.getVert 8))
      (act R h (act R g (p.walk.getVert 7))) =
      edgeCommutator R (act R g (p.walk.getVert 8)) t := by
    change (edgeCommutator R _ _).map _ = _ at he
    have heq := RegularPaths.edgeCommutator_act h
      (act R g (p.walk.getVert 8)) (act R g (p.walk.getVert 7))
    rw [hfix] at heq
    exact heq.trans he
  refine ⟨{
    conjugator := h
    conjugator_local := hh
    neighbor := act R h (act R g (p.walk.getVert 7))
    neighbor_eq := rfl
    first_adjacent := ?_
    second_adjacent := ?_
    nonnormalization := ?_
    critical_distance := ?_
    critical_noncontainment := ?_ }⟩
  · have h1 : Adjacent R (act R g (p.walk.getVert 8)) (act R g (p.walk.getVert 7)) :=
      (adjacent_act_iff R g _ _).mpr ((cosetGraph_adj R _ _).mp
        (p.walk.adj_getVert_succ (i := 7) (by rw [p.length_eq]; decide)).symm)
    simpa only [hfix] using (adjacent_act_iff R h _ _).mpr h1
  · exact (adjacent_act_iff R h _ _).mpr ((adjacent_act_iff R g _ _).mpr
      ((cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i := 6) (by rw [p.length_eq]; decide))))
  · rwa [hedge]
  · exact r.critical.1.trans ((geometry.distance_constant _ r.start_color).trans earlier.distance)
  · exact r.critical.2


namespace Witness
variable {a : Vertex R} {p : Higher.SourcePath a} {g : stabilizer R a}

/-- The selected source vertex a-6. -/
def endpoint (w : Witness p g) : Vertex R :=
  act R w.conjugator (act R g (p.walk.getVert 6))

/-- The replacement endpoint is an M-vertex. -/
theorem endpoint_color (w : Witness p g) : color R w.endpoint = false := by
  rw [endpoint, action_preserves_color, action_preserves_color]
  exact (RegularPaths.walk_vertex_color p.start_color p.walk
    (by rw [p.length_eq]; decide)).mpr (by decide)

/-- The selected endpoint lies exactly two steps from d^g. -/
theorem dist_endpoint_pivot (w : Witness p g) :
    (cosetGraph R).dist w.endpoint (act R g (p.walk.getVert 8)) = 2 := by
  have h := dist_act R w.conjugator (act R g (p.walk.getVert 6)) (act R g (p.walk.getVert 8))
  have hf : act R w.conjugator (act R g (p.walk.getVert 8)) =
      act R g (p.walk.getVert 8) := w.conjugator_local
  rw [hf, dist_act] at h
  exact h.trans (p.dist (by decide) (by decide))

/-- Distance alone puts both seeds Z_a and Z_(c^g) into the selected endpoint's
kernel. This is the final containment on p.899, before using the equal-Z case. -/
theorem seed_join_le_Q (w : Witness p g) (earlier : Earlier R geometry) :
    Z R a ⊔ Z R (act R g (p.walk.getVert 6)) ≤ Q R w.endpoint := by
  have ha : color R a = false := by
    have hc := (RegularPaths.walk_vertex_color p.start_color p.walk
      (by rw [p.length_eq]; decide)).mpr (by decide : Even 4)
    rwa [p.center_eq] at hc
  have hc : color R (act R g (p.walk.getVert 6)) = false := by
    rw [action_preserves_color]
    exact (RegularPaths.walk_vertex_color p.start_color p.walk
      (by rw [p.length_eq]; decide)).mpr (by decide)
  have hfix : act R g a = a := g.property
  have hda : (cosetGraph R).dist (act R g (p.walk.getVert 8)) a = 4 := by
    have h := dist_act R (g : FreeAmalgam R) (p.walk.getVert 8) a
    rw [hfix] at h
    rw [h, SimpleGraph.dist_comm]
    simpa only [p.center_eq] using p.dist (i := 4) (j := 8) (by decide) (by decide)
  have hdc : (cosetGraph R).dist (act R g (p.walk.getVert 8))
      (act R g (p.walk.getVert 6)) = 2 := by
    rw [dist_act, SimpleGraph.dist_comm]
    exact p.dist (by decide) (by decide)
  apply sup_le
  · apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a ha)
    rw [geometry.distance_constant a ha]
    change _ < geometry.b R
    rw [earlier.distance, SimpleGraph.dist_comm]
    have ht := (cosetGraph_connected R).dist_triangle
      (u := w.endpoint) (v := act R g (p.walk.getVert 8)) (w := a)
    rw [w.dist_endpoint_pivot, hda] at ht
    omega
  · apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ hc)
    rw [geometry.distance_constant _ hc]
    change _ < geometry.b R
    rw [earlier.distance, SimpleGraph.dist_comm]
    have ht := (cosetGraph_connected R).dist_triangle
      (u := w.endpoint) (v := act R g (p.walk.getVert 8))
      (w := act R g (p.walk.getVert 6))
    rw [w.dist_endpoint_pivot, hdc] at ht
    omega

/-- Reversed criticality contradicts the two-seed containment that the equal-Z
case must establish. No equal-edge comparison is assumed or asserted here. -/
theorem opposite_not_le_seed_join {source : LocalSource L R}
    (w : Witness p g) (common : CommonFacts R source geometry) (earlier : Earlier R geometry) :
    ¬ Z R (p.walk.getVert 6) ≤ Z R a ⊔ Z R (act R g (p.walk.getVert 6)) := by
  have hc := (RegularPaths.walk_vertex_color p.start_color p.walk
    (by rw [p.length_eq]; decide)).mpr (by decide : Even 6)
  have hcrit : CriticalPair R w.endpoint (p.walk.getVert 6)
      (geometry.exists_critical _ w.endpoint_color) := by
    refine ⟨?_, w.critical_noncontainment⟩
    rw [geometry.distance_constant _ w.endpoint_color]
    exact w.critical_distance.trans earlier.distance.symm
  have hn := (common.critical_reverse _ w.endpoint_color _ hc hcrit).2
  exact fun h => hn (h.trans (w.seed_join_le_Q earlier))

/-- Apply (4.5.4)(i) to the literal selected endpoint and c. Its sole extra
premise is the preceding (4.5.1)(i), owned by the early-layer assembly. -/
theorem commutator_le_H (w : Witness p g) (earlier : Earlier R geometry)
    (hcomm : ⁅V R a, V R (p.walk.getVert 8)⁆ = H R a ⊓ H R (p.walk.getVert 8)) :
    ⁅Z R w.endpoint, Z R (p.walk.getVert 6)⁆ ≤ H R (p.walk.getVert 8) := by
  have ha : color R a = false := by
    have hc := (RegularPaths.walk_vertex_color p.start_color p.walk
      (by rw [p.length_eq]; decide)).mpr (by decide : Even 4)
    rwa [p.center_eq] at hc
  have hd := (RegularPaths.walk_vertex_color p.start_color p.walk
    (by rw [p.length_eq]; decide)).mpr (by decide : Even 8)
  have hda : (cosetGraph R).dist (p.walk.getVert 8) a ≤ 4 := by
    simpa only [p.center_eq, SimpleGraph.dist_comm] using
      (p.dist (i := 4) (j := 8) (by decide) (by decide)).le
  have hcV : Z R (p.walk.getVert 6) ≤ V R a :=
    le_iSup_of_le _ (le_iSup_of_le p.two_step_distances.1.le le_rfl)
  have hrV : Z R w.endpoint ≤ V R (act R g (p.walk.getVert 8)) :=
    le_iSup_of_le _ (le_iSup_of_le w.dist_endpoint_pivot.le le_rfl)
  have hrS : Z R w.endpoint ≤
      NormalizerTransfer.conjugatesIn (V R (p.walk.getVert 8)) (stabilizer R a) := by
    rw [V_act] at hrV
    exact hrV.trans (le_iSup (fun k : stabilizer R a =>
      NormalizerTransfer.rightConjugate (V R (p.walk.getVert 8)) k) g)
  rw [commutator_comm]
  exact (commutator_mono hcV hrS).trans
    ((Higher.radius_orbit_commutator earlier ha hd hda hcomm).le.trans inf_le_right)

end Witness
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Replacement
