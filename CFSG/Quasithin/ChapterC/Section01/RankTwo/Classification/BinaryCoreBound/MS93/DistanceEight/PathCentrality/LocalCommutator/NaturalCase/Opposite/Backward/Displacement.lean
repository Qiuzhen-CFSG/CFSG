module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Backward.Selection

/-!
# Bounds for the backward displacement in MS93 (4.4.1)(1)

The predecessor radius is contained in the initial edge kernel. Consequently
its commutator with the starting Z-layer lies in the initial edge, which has
order at most four. The missing source lower bound of four therefore implies
the exact closing displacement identity.

The forward calculation also supplies a lower bound at its own center and
endpoint: every retained continuation lies within radius two of that endpoint,
and its commutator identity puts it in the endpoint Z-layer. Their generated
order-four subgroup lies in the required intersection. This lemma may be
applied to a newly selected configuration only after that selection is proved.
It does not assert that a shifted critical path is automatically SelectedPath.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1), claim (1), p.891.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite
variable {M : Type*} [Group M] {L R : Subgroup M}
variable {source : LocalSource L R} {geometry : Geometry R} {a c : Vertex R}

namespace SelectedPath
variable (s : SelectedPath R geometry a c)

/-- The predecessor radius lies in the first-edge kernel. -/
theorem backward_displacement_le_edge (hb : 4 < geometry.b R) :
    ⁅Z R s.start, V R s.predecessor⁆ ≤ s.edge :=
  commutator_mono le_rfl (s.predecessor_radius_le_first_Q hb)

/-- The source lower bound fills the original edge, whose order is at most four. -/
theorem backward_displacement_eq_of_card_lower [Finite M]
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (hlower : 4 ≤ Nat.card (⁅Z R s.start, V R s.predecessor⁆ ⊓
      Z R s.predecessor : Subgroup (FreeAmalgam R))) :
    ⁅Z R s.start, V R s.predecessor⁆ ⊓ Z R s.predecessor = s.edge := by
  have hU : s.edge ≤ U R s.start :=
    Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (moduleFacts common) s.start s.first s.path.start_color
      (s.start_adjacent_first (by omega))
  let : Finite (U R s.start) := Nat.finite_of_card_ne_zero
    (by rw [common.natural.card_at s.start s.path.start_color]; decide)
  let : Finite s.edge := Finite.of_injective (inclusion hU) (inclusion_injective _)
  have hupper : Nat.card s.edge ≤ 4 :=
    Escape.EdgeTransfer.edge_displacement_card_le_four common.large_distance
      (moduleFacts common) s.start s.first s.path.start_color
      (s.start_adjacent_first (by omega))
  exact eq_of_le_of_card_ge (inf_le_left.trans (s.backward_displacement_le_edge hb))
    (hupper.trans hlower)

end SelectedPath

namespace SelectedPath
variable (s : SelectedPath R geometry a c)

theorem Continuation.vertex_distance_le_two (w : s.Continuation) :
    (cosetGraph R).dist w.vertex s.endpoint ≤ 2 := by
  have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr
    (adjacent_symm R w.adjacent_vertex))
  have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr
    (adjacent_symm R w.adjacent_endpoint))
  have ht := (cosetGraph_connected R).dist_triangle
    (u := w.vertex) (v := w.intermediate) (w := s.endpoint)
  omega

/-- Each retained endpoint commutator lies in the literal radius displacement
and in the endpoint Z-layer. -/
theorem ForwardFacts.endpointSpan_le_displacement (f : s.ForwardFacts) :
    s.endpointSpan ≤ ⁅Z R s.center, V R s.endpoint⁆ ⊓ Z R s.endpoint := by
  apply iSup_le
  intro w
  apply le_inf
  · apply commutator_mono le_rfl
    exact le_iSup_of_le w.vertex (le_iSup_of_le (w.vertex_distance_le_two s) le_rfl)
  · rw [f.commutator_eq w]
    apply inf_le_left.trans
    apply le_normalizer_iff_commutator_le_left.mp
    apply le_trans (show Q R w.intermediate ≤ stabilizer R s.endpoint from
      fun _ hx => hx.2 s.endpoint (adjacent_symm R w.adjacent_endpoint))
    exact Z_normalized R s.endpoint

/-- The forward order-four span yields the source radius-displacement lower
bound at this selected path's center and endpoint. -/
theorem ForwardFacts.displacement_card_lower [Finite M] (f : s.ForwardFacts) :
    4 ≤ Nat.card (⁅Z R s.center, V R s.endpoint⁆ ⊓
      Z R s.endpoint : Subgroup (FreeAmalgam R)) := by
  let := finite_stabilizer R s.endpoint
  let K := ⁅Z R s.center, V R s.endpoint⁆ ⊓ Z R s.endpoint
  let : Finite K := Finite.of_injective
    (inclusion (show K ≤ stabilizer R s.endpoint from inf_le_right.trans
      (Z_le_stabilizer R s.endpoint))) (inclusion_injective _)
  rw [← f.generated_card]
  exact card_le_of_le (f.endpointSpan_le_displacement s)

end SelectedPath
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite
