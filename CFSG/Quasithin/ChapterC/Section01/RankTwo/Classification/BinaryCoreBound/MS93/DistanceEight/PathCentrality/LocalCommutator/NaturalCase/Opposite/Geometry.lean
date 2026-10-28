module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Source

/-!
# The two escape contradictions in the opposite natural orientation

For a selected critical path, its third vertex is close enough to the endpoint
that the endpoint radius group lies in the third-vertex kernel. Thus the retained
centralizer selection turns centralization of the selected edge into the exact
radius containment forbidden by CommonFacts.escape on the reversed critical pair.
The second vertex has distance two from that pair's endpoint; both required
geodesic distance equations are checked explicitly.

If the edge lies in the endpoint radius group, b > 4 makes it central there.
If it lies in the Z-layer two steps before the endpoint, the same inequality
puts the endpoint radius group in that vertex's kernel and again proves
centralization. These are precisely the final geometric steps of the first
and second contradictions on p.891. The backward witness also constructs the
new critical path from its two actual edges and noncontainment.

The seed selection and displacement identities remain explicit intermediate
inputs, with no unconditional constructor asserted here. The diagnostic
`center_endpoint_commutator_eq_bot` checks the printed endpoint-index typo
explained in Source.lean; it is not a counterexample to the intended theorem.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1), claim (1), p.891,
using the escape statement (4.3) and the critical-path definitions on p.855.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.SelectedPath
variable {M : Type*} [Group M] {L R : Subgroup M}
variable {source : LocalSource L R} {geometry : Geometry R} {a c : Vertex R}
variable (s : SelectedPath R geometry a c)

theorem center_color (hb : 2 ≤ geometry.b R) : color R s.center = false :=
  (s.path.vertex_color (by rw [s.path.length_eq_b]; exact hb)).mpr (by decide)

theorem predecessor_color : color R s.predecessor = false := by
  have he : Even s.path.walk.length := by
    rw [s.path.shortest, s.path.critical.1]
    exact geometry.even s.start s.path.start_color
  apply (s.path.vertex_color (Nat.sub_le _ _)).mpr
  rw [Nat.even_iff] at he ⊢
  omega

theorem center_distance (hb : 2 ≤ geometry.b R) :
    (cosetGraph R).dist s.start s.center = 2 :=
  s.path.dist_start (by rw [s.path.length_eq_b]; exact hb)

theorem predecessor_distance (hb : 2 ≤ geometry.b R) :
    (cosetGraph R).dist s.predecessor s.endpoint = 2 := by
  rw [s.path.dist_end, s.path.length_eq_b]
  omega

theorem endpoint_V_le_third_Q (hb : 4 < geometry.b R) :
    V R s.endpoint ≤ Q R s.third := by
  apply V_le_Q_of_dist_add_two_lt R s.path.end_color
  rw [SimpleGraph.dist_comm, s.path.dist_end, s.path.length_eq_b]
  omega

theorem endpoint_V_le_predecessor_Q (hb : 4 < geometry.b R) :
    V R s.endpoint ≤ Q R s.predecessor := by
  apply V_le_Q_of_dist_add_two_lt R s.path.end_color
  rw [SimpleGraph.dist_comm, s.predecessor_distance (by omega)]
  exact hb

/-- The literal printed commutator uses a pair strictly closer than b. -/
theorem center_endpoint_commutator_eq_bot (hb : 2 ≤ geometry.b R) :
    ⁅Z R s.center, Z R s.endpoint⁆ = ⊥ := by
  have hZ : Z R s.endpoint ≤ Q R s.center := by
    apply Z_le_Q_of_dist_lt R s.endpoint
      (geometry.exists_critical s.endpoint s.path.end_color)
    rw [geometry.distance_constant s.endpoint s.path.end_color,
      SimpleGraph.dist_comm, s.path.dist_end, s.path.length_eq_b]
    change geometry.b R - 2 < geometry.b R
    omega
  exact le_bot_iff.mp ((commutator_mono le_rfl hZ).trans
    (geometry.centralizes s.center (s.center_color hb)).le)

/-- Escape is applied to the reversed actual critical pair at its correct predecessor. -/
theorem endpoint_radius_escapes (common : CommonFacts R source geometry)
    (hb : 2 ≤ geometry.b R) : ¬ V R s.endpoint ≤ Q R s.center := by
  apply common.escape s.endpoint s.path.end_color s.start
    (common.critical_reverse s.start s.path.start_color s.endpoint s.path.end_color s.path.critical)
    s.center
  · rw [SimpleGraph.dist_comm]
    exact s.center_distance hb
  · rw [SimpleGraph.dist_comm (u := s.endpoint) (v := s.center), s.path.dist_end,
      SimpleGraph.dist_comm (u := s.endpoint) (v := s.start), ← s.path.shortest,
      s.path.length_eq_b]
    omega

theorem false_of_edge_centralizes_endpoint_radius (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R)
    (h : s.edge ≤ centralizer (V R s.endpoint : Set (FreeAmalgam R))) : False := by
  apply s.endpoint_radius_escapes common (by omega)
  exact (le_inf (s.endpoint_V_le_third_Q hb) (le_centralizer_iff.mp h)).trans
    s.centralizer_selection

/-- The first escape contradiction after a noncritical forward continuation. -/
theorem edge_not_le_endpoint_radius (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) : ¬ s.edge ≤ V R s.endpoint := by
  intro h
  let := V_abelian_of_four_lt R s.path.end_color hb
  exact s.false_of_edge_centralizes_endpoint_radius common hb
    (h.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance))

/-- The second escape contradiction after the backward displacement calculation. -/
theorem edge_not_le_predecessor_Z (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) : ¬ s.edge ≤ Z R s.predecessor := by
  intro h
  apply s.false_of_edge_centralizes_endpoint_radius common hb
  exact h.trans ((commutator_eq_bot_iff_le_centralizer.mp
    (geometry.centralizes s.predecessor s.predecessor_color)).trans
      (centralizer_le (s.endpoint_V_le_predecessor_Q hb)))

namespace BackwardClosing
variable {s} (w : s.BackwardClosing)

/-- The selected backward noncontainment gives an actual new critical path. -/
def shifted (hb : 2 ≤ geometry.b R) :
    CriticalPath R geometry w.vertex s.predecessor := by
  have hc : color R w.vertex = false := by
    rw [← w.start_image, action_preserves_color]
    exact s.path.start_color
  let q : (cosetGraph R).Walk w.vertex s.start :=
    .cons ((cosetGraph_adj R _ _).mpr w.adjacent_start)
      (.cons ((cosetGraph_adj R _ _).mpr w.adjacent_center) .nil)
  exact s.path.prepend_two hb hc q rfl w.noncontainment

include w in
/-- Apply the second contradiction to the source backward displacement identity. -/
theorem false_of_closing (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) : False :=
  s.edge_not_le_predecessor_Z common hb (w.displacement.symm.le.trans inf_le_right)

end BackwardClosing
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.SelectedPath
