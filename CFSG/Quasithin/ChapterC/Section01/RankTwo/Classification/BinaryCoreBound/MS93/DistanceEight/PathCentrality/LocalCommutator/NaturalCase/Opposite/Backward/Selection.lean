module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Consequences.Geometry

/-!
# The backward critical choice in MS93 (4.4.1)(1)

The radius group at the first edge lies in the kernel two steps before the
old endpoint. Since the start radius escapes that kernel, the decomposition
of the radius as its moving layer joined with the edge radius makes the
moving layer escape too. Transport the supplied moving-span containment to
the start, and select an escaping generator in the actual stabilizer orbit.
The output retains both backward edges and the same ordered-pair conjugator,
including the image of the intermediate vertex. Noncontainment constructs a
new shortest critical path, whose vertex at index two is the old start.

The required moving-span containment is the final field of ForwardFacts.
No backward displacement or order-four lower bound is assumed or proved in
this module; that calculation remains separate.
Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1), claim (1), p.891.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite
variable {M : Type*} [Group M] {L R : Subgroup M}
variable {source : LocalSource L R} {geometry : Geometry R} {a c : Vertex R}

namespace SelectedPath
variable (s : SelectedPath R geometry a c)

/-- The actual backward selection, before its displacement calculation. -/
structure BackwardChoice where
  intermediate : Vertex R
  vertex : Vertex R
  adjacent_start : Adjacent R vertex intermediate
  adjacent_center : Adjacent R intermediate s.start
  conjugator : FreeAmalgam R
  start_image : act R conjugator s.start = vertex
  center_image : act R conjugator s.center = s.start
  first_image : act R conjugator s.first = intermediate
  noncontainment : ¬ Z R vertex ≤ Q R s.predecessor

theorem start_adjacent_first (hb : 2 ≤ geometry.b R) : Adjacent R s.start s.first := by
  have hl := s.path.length_eq_b
  apply (cosetGraph_adj R _ _).mp
  simpa only [SimpleGraph.Walk.getVert_zero] using
    s.path.walk.adj_getVert_succ (i := 0) (show 0 < s.path.walk.length by omega)

theorem first_adjacent_center (hb : 2 ≤ geometry.b R) : Adjacent R s.first s.center := by
  have hl := s.path.length_eq_b
  exact (cosetGraph_adj R _ _).mp (s.path.walk.adj_getVert_succ (i := 1) (by omega))

private theorem first_predecessor_distance_le (hb : 4 < geometry.b R) :
    (cosetGraph R).dist s.first s.predecessor ≤ s.path.walk.length - 3 := by
  have hl := s.path.length_eq_b
  have h := SimpleGraph.dist_le ((s.path.walk.take (s.path.walk.length - 2)).drop 1)
  simpa only [SimpleGraph.Walk.take_getVert, inf_eq_right.mpr (show 1 ≤ s.path.walk.length - 2 by omega),
    SimpleGraph.Walk.drop_length, SimpleGraph.Walk.take_length,
    inf_eq_left.mpr (Nat.sub_le _ _), Nat.sub_sub] using h

theorem first_radius_le_predecessor_Q (hb : 4 < geometry.b R) :
    V R s.first ≤ Q R s.predecessor := by
  apply Escape.Initial.Consequences.V_le_of_h_neighbors s.path.start_color
    (s.start_adjacent_first (by omega))
  intro d hd
  have hc : color R d = false := by
    have ht := adjacent_color_ne R (s.start_adjacent_first (by omega))
    have hd' := adjacent_color_ne R hd
    rw [s.path.start_color] at ht
    cases h : color R d <;> cases h' : color R s.first <;> simp_all
  apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hc)
  rw [geometry.distance_constant d hc]
  have hdt := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hd)
  have htri := (cosetGraph_connected R).dist_triangle
    (u := d) (v := s.first) (w := s.predecessor)
  have hseg := s.first_predecessor_distance_le hb
  have hl := s.path.length_eq_b
  change (cosetGraph R).dist d s.predecessor < geometry.b R
  omega

theorem predecessor_radius_le_first_Q (hb : 4 < geometry.b R) :
    V R s.predecessor ≤ Q R s.first := by
  apply V_le_Q_of_dist_add_two_lt R s.predecessor_color
  have hd := s.first_predecessor_distance_le hb
  rw [SimpleGraph.dist_comm] at hd
  have hl := s.path.length_eq_b
  omega

/-- Escape and the edge-radius decomposition force the moving layer to escape. -/
theorem start_moving_not_le_predecessor_Q [Finite M]
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R) :
    ¬ Vcirc R s.start ≤ Q R s.predecessor := by
  intro h
  apply common.escape s.start s.path.start_color s.endpoint s.path.critical s.predecessor
    (s.predecessor_distance (by omega))
    (by rw [s.path.dist_start (Nat.sub_le _ _), ← s.path.shortest]
        have hl := s.path.length_eq_b
        omega)
  rw [Escape.Initial.Consequences.radius_eq_moving_sup_edge source s.path.start_color
    (s.start_adjacent_first (by omega))]
  exact sup_le h (s.first_radius_le_predecessor_Q hb)

private theorem exists_center_conjugator (hb : 2 ≤ geometry.b R) :
    ∃ g : FreeAmalgam R, act R g s.center = s.start := by
  obtain ⟨x, hx⟩ := exists_mVertex_of_color R (s.center_color hb)
  obtain ⟨y, hy⟩ := exists_mVertex_of_color R s.path.start_color
  refine ⟨x⁻¹ * y, ?_⟩
  rw [hx, hy, act_mVertex, mul_inv_cancel_left]

/-- The forward moving-span containment selects a backward critical pair in
the prescribed ordered-pair orbit. -/
theorem backwardChoice_nonempty [Finite M] (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (hspan : Vcirc R s.center ≤ localZSpan R s.start s.center) :
    Nonempty s.BackwardChoice := by
  classical
  obtain ⟨g, hg⟩ := s.exists_center_conjugator (by omega)
  have hm : Vcirc R s.start ≤ localZSpan R (act R g s.start) s.start := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hspan
    rwa [← Vcirc_act, ← CriticalCase.localZSpan_act, hg] at hh
  obtain ⟨k, hk⟩ : ∃ k : stabilizer R s.start,
      ¬ Z R (act R k (act R g s.start)) ≤ Q R s.predecessor := by
    by_contra! hn
    exact s.start_moving_not_le_predecessor_Q common hb (hm.trans (iSup_le hn))
  have hfix : act R k s.start = s.start := k.property
  have hcenter : act R (g * k) s.center = s.start := by rw [act_mul, hg, hfix]
  refine ⟨{
    intermediate := act R (g * k) s.first
    vertex := act R k (act R g s.start)
    adjacent_start := ?_
    adjacent_center := ?_
    conjugator := g * k
    start_image := act_mul R g k s.start
    center_image := hcenter
    first_image := rfl
    noncontainment := hk }⟩
  · rw [← act_mul]
    exact (adjacent_act_iff R _ _ _).mpr (s.start_adjacent_first (by omega))
  · simpa only [hcenter] using
      (adjacent_act_iff R (g * k) _ _).mpr (s.first_adjacent_center (by omega))

namespace BackwardChoice
variable {s} (w : s.BackwardChoice)

theorem vertex_color : color R w.vertex = false := by
  rw [← w.start_image, action_preserves_color]
  exact s.path.start_color

theorem moving_le_span (hspan : Vcirc R s.center ≤ localZSpan R s.start s.center) :
    Vcirc R s.start ≤ localZSpan R w.vertex s.start := by
  have hh := map_mono (f := (MulAut.conj w.conjugator⁻¹).toMonoidHom) hspan
  rwa [← Vcirc_act, ← CriticalCase.localZSpan_act, w.start_image, w.center_image] at hh

/-- Build the genuine shifted critical path from the two retained edges. -/
def shifted (hb : 2 ≤ geometry.b R) : CriticalPath R geometry w.vertex s.predecessor := by
  let q : (cosetGraph R).Walk w.vertex s.start :=
    .cons ((cosetGraph_adj R _ _).mpr w.adjacent_start)
      (.cons ((cosetGraph_adj R _ _).mpr w.adjacent_center) .nil)
  exact s.path.prepend_two hb w.vertex_color q rfl w.noncontainment

theorem shifted_center (hb : 2 ≤ geometry.b R) :
    (w.shifted hb).walk.getVert 2 = s.start := by
  simp [shifted, CriticalPath.prepend_two, id]

end BackwardChoice
end SelectedPath
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite
