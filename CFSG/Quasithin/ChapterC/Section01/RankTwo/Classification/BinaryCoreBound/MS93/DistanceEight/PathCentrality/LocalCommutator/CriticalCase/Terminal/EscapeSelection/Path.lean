module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.EscapeSelection.Fixedness


/-!
# The vertex four steps before the terminal endpoint

The original and shifted critical paths share the vertex e-4. Their exact
lengths put its radius group in Q_c and Z_d in its own kernel. Under the
all-rho fixedness assumption, these two containments trap [Z_d,V_(e-4)]
inside both [Z_d,Q_c] and B_(e-4). The reverse containment and centrality
at e remain the substantial missing steps of the printed contradiction.

The backward displacement has order four: it properly contains the critical
commutator of order two, since otherwise it would lie in V_(e-2), contrary
to the witness's nontrivial triple commutator.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.1), p.892, the all-rho paragraph after claim (3).
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.EscapeSelection
variable {M : Type*} [Group M] {L R : Subgroup M} {source : LocalSource L R}
  {geometry : Geometry R} {a c : Vertex R}

/-- The source vertex alpha'-4 on the retained original critical path. -/
def fourBeforeEndpoint (w : BackwardWitness R geometry a c) : Vertex R :=
  w.path.walk.getVert (w.path.walk.length - 4)

/-- Subtracting four preserves the endpoint M-color. -/
theorem fourBeforeEndpoint_color (w : BackwardWitness R geometry a c) :
    color R (fourBeforeEndpoint w) = false := by
  apply (w.path.vertex_color (Nat.sub_le _ _)).mpr
  have he : Even w.path.walk.length := by
    rw [w.path.shortest, w.path.critical.1]
    exact geometry.even c w.path.start_color
  rw [Nat.even_iff] at he ⊢
  omega

/-- Its position on the original path is b-4. -/
theorem fourBeforeEndpoint_distance_start (w : BackwardWitness R geometry a c) :
    (cosetGraph R).dist c (fourBeforeEndpoint w) = geometry.b R - 4 := by
  rw [fourBeforeEndpoint, w.path.dist_start (Nat.sub_le _ _), w.path.length_eq_b]

/-- It is exactly four edges before the endpoint. -/
theorem fourBeforeEndpoint_distance_end (hb : 4 ≤ geometry.b R)
    (w : BackwardWitness R geometry a c) :
    (cosetGraph R).dist (fourBeforeEndpoint w) w.endpoint = 4 := by
  rw [fourBeforeEndpoint, w.path.dist_end, w.path.length_eq_b]
  omega

/-- The shifted critical path puts it b-2 edges from the backward vertex. -/
theorem fourBeforeEndpoint_distance_backward (hb : 4 ≤ geometry.b R)
    (ha : color R a = false) (w : BackwardWitness R geometry a c) :
    (cosetGraph R).dist w.backward (fourBeforeEndpoint w) = geometry.b R - 2 := by
  let p := w.shifted ha (by omega : 2 ≤ geometry.b R)
  have ho := w.shifted_overlap ha (by omega : 2 ≤ geometry.b R)
    (i := w.path.walk.length - 4) (by omega)
  have hi : w.path.walk.length - 4 + 2 ≤ p.walk.length := by
    rw [p.length_eq_b, w.path.length_eq_b]
    omega
  have hh := p.dist_start hi
  rw [ho] at hh
  change (cosetGraph R).dist w.backward (fourBeforeEndpoint w) = _ at hh
  have he : w.path.walk.length - 4 + 2 = geometry.b R - 2 := by
    rw [w.path.length_eq_b]
    omega
  exact hh.trans he

/-- Critical minimality puts the backward Z in the kernel at e-4. -/
theorem backward_Z_le_fourBeforeEndpoint_kernel (hb : 4 < geometry.b R)
    (ha : color R a = false) (w : BackwardWitness R geometry a c) :
    Z R w.backward ≤ Q R (fourBeforeEndpoint w) := by
  apply Z_le_Q_of_dist_lt R w.backward (geometry.exists_critical _ (w.backward_color ha))
  rw [geometry.distance_constant _ (w.backward_color ha),
    fourBeforeEndpoint_distance_backward (by omega) ha w]
  change geometry.b R - 2 < geometry.b R
  omega

/-- Its radius group lies in the original center kernel. -/
theorem fourBeforeEndpoint_V_le_center_kernel [Finite M]
    (hb : 4 < geometry.b R) (w : BackwardWitness R geometry a c) :
    V R (fourBeforeEndpoint w) ≤ Q R c := by
  apply V_le_Q_of_dist_add_two_lt R (fourBeforeEndpoint_color w)
  rw [SimpleGraph.dist_comm, fourBeforeEndpoint_distance_start w]
  omega

/-- The witness forces the upper bound four for the displacement to be exact. -/
theorem backward_displacement_card_four [Finite M]
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (ha : color R a = false) (hd : (cosetGraph R).dist a c = 2)
    (w : BackwardWitness R geometry a c) :
    Nat.card (⁅Z R w.backward, Q R c⁆ : Subgroup (FreeAmalgam R)) = 4 := by
  let E := ⁅Z R w.backward, Q R c⁆
  let D := ⁅Z R w.backward, Z R w.predecessor⁆
  have hDE : D ≤ E := commutator_mono le_rfl
    (w.predecessor_Z_le_center_kernel (by omega))
  have hES : E ≤ stabilizer R w.backward :=
    (displacement_le_U common (w.backward_color ha) (w.backward_distance hd)).trans
      ((U_le_Z R _).trans (Z_le_stabilizer R _))
  let := finite_stabilizer R w.backward
  let : Finite E := Finite.of_injective (inclusion hES) (inclusion_injective hES)
  have hD : Nat.card D = 2 := critical_commutator_card common (w.shifted ha (by omega))
  have hdvd : 2 ∣ Nat.card E := hD ▸ card_dvd_of_le hDE
  have hE := displacement_card_le_four common (w.backward_color ha) (w.backward_distance hd)
  have hpos : 0 < Nat.card E := Nat.card_pos
  have hne : Nat.card E ≠ 2 := by
    intro htwo
    have heq : D = E := eq_of_le_of_card_ge hDE (by rw [hD, htwo])
    apply w.displacement_not_le_predecessor_V hb
    change E ≤ V R w.predecessor
    rw [← heq]
    exact (le_normalizer_iff_commutator_le_right.mp
      (((w.shifted ha (by omega)).reverse common).endpoint_Z_le_start_stabilizer
        (by omega) |>.trans (Z_normalized R _))).trans (Z_le_VBall R _ 2)
  change Nat.card E = 4
  change Nat.card E ≤ 4 at hE
  omega

/-- The two source containments for the commutator at e-4, on the actual
path and with only the original all-rho fixedness assumption. -/
theorem fourBeforeEndpoint_commutator_bounds [Finite M]
    (hb : 4 < geometry.b R) (ha : color R a = false)
    (w : BackwardWitness R geometry a c)
    (hall : ∀ rho, (cosetGraph R).dist c rho = 2 →
      ⁅Z R rho, Q R c⁆ ≤ B R c (geometry.Z_normal c)) :
    ⁅Z R w.backward, V R (fourBeforeEndpoint w)⁆ ≤
      ⁅Z R w.backward, Q R c⁆ ∧
    ⁅Z R w.backward, V R (fourBeforeEndpoint w)⁆ ≤
      B R (fourBeforeEndpoint w) (geometry.Z_normal _) := by
  refine ⟨commutator_mono le_rfl (fourBeforeEndpoint_V_le_center_kernel hb w), ?_⟩
  apply (commutator_mono (backward_Z_le_fourBeforeEndpoint_kernel hb ha w) le_rfl).trans
  rw [commutator_comm]
  exact radius_displacement_le_B (by omega) (fourBeforeEndpoint_color w)
    (all_fixed_at_any_center (by omega) w.path.start_color hall (fourBeforeEndpoint_color w))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.EscapeSelection
