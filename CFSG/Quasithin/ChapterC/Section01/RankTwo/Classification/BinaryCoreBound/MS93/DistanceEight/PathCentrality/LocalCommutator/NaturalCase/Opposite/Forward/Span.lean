module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Forward.Pointwise

/-!
# The full forward orbit span and its commutators

All continuations have the same endpoint-stabilizer orbit span V0. The
right-action conjugator comparing two choices is g inverse times g prime.
Every generator, including nonavoiding ones, has distance at most b from c,
so V0 lies in G_c. The transported full displacements lie in U_b.

These bounds put both [Z_c,V0] and [V_c intersect Q_b,V0] in U_b intersect Q_a.
The elementary radius group V_b centralizes this kernel intersection, allowing
the bounds on generators to pass to V0. All avoiding critical commutators lie
in [Z_c,V0]. Thus the remaining generated-plane identity supplies the exact
center commutator and the literal radius-commutator field of ForwardFacts.
The generated-plane identity is an explicit undischarged premise here.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)(1), printed p.891.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.SelectedPath
variable {M : Type*} [Group M] {L R : Subgroup M}
variable {source : LocalSource L R} {geometry : Geometry R} {a c : Vertex R}
variable {s : SelectedPath R geometry a c}
namespace Continuation
variable (w : s.Continuation)

/-- Every continuation defines the same literal local orbit span. -/
theorem span_eq (w' : s.Continuation) : s.continuationSpan w = s.continuationSpan w' := by
  let h := w.conjugator⁻¹ * w'.conjugator
  have hfix : act R h s.endpoint = s.endpoint := by
    calc
      _ = act R h (act R w.conjugator s.center) := congrArg (act R h) w.center_image.symm
      _ = act R (w.conjugator * h) s.center := (act_mul R _ _ _).symm
      _ = s.endpoint := by simp only [h, mul_inv_cancel_left, w'.center_image]
  have hmove : act R h w.vertex = w'.vertex := by
    calc
      _ = act R h (act R w.conjugator s.start) := congrArg (act R h) w.start_image.symm
      _ = act R (w.conjugator * h) s.start := (act_mul R _ _ _).symm
      _ = w'.vertex := by simp only [h, mul_inv_cancel_left, w'.start_image]
  change localZSpan R w.vertex s.endpoint = localZSpan R w'.vertex s.endpoint
  rw [← hmove]
  exact (CriticalCase.span_eq_of_local_conjugator hfix).symm

/-- Distance two is retained by every element of the full endpoint stabilizer. -/
theorem orbit_distance (hb : 2 ≤ geometry.b R) (g : stabilizer R s.endpoint) :
    (cosetGraph R).dist (act R g w.vertex) s.endpoint = 2 := by
  have hh := dist_act R (g : FreeAmalgam R) w.vertex s.endpoint
  rw [show act R g s.endpoint = s.endpoint from g.property] at hh
  exact hh.trans (w.endpoint_distance hb)

/-- All generators of V0, including the nonavoiding ones, act at the center. -/
theorem orbit_Z_le_center_stabilizer (hb : 2 ≤ geometry.b R)
    (g : stabilizer R s.endpoint) : Z R (act R g w.vertex) ≤ stabilizer R s.center := by
  apply geometry.Z_le_stabilizer_of_dist_le_b _
    (by rw [action_preserves_color]; exact w.vertex_color)
  have htri := (cosetGraph_connected R).dist_triangle
    (u := act R g w.vertex) (v := s.endpoint) (w := s.center)
  rw [w.orbit_distance hb, SimpleGraph.dist_comm (u := s.endpoint), s.path.dist_end,
    s.path.length_eq_b] at htri
  change (cosetGraph R).dist (act R g w.vertex) s.center ≤ geometry.b R
  omega

/-- V0 is local at the original center, despite being generated at the endpoint. -/
theorem span_le_center_stabilizer (hb : 2 ≤ geometry.b R) :
    s.continuationSpan w ≤ stabilizer R s.center :=
  iSup_le fun g => w.orbit_Z_le_center_stabilizer hb g

/-- The full displacement of every orbit generator stays in the endpoint natural group. -/
theorem orbit_displacement_le_U [Finite M] (common : CommonFacts R source geometry)
    (hb : 2 ≤ geometry.b R) (g : stabilizer R s.endpoint) :
    ⁅Z R (act R g w.vertex), Q R s.endpoint⁆ ≤ U R s.endpoint := by
  have h : ⁅Z R w.vertex, Q R s.endpoint⁆ ≤ U R s.endpoint := by
    rw [w.displacement_eq_edge hb]
    exact Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (moduleFacts common) s.endpoint w.intermediate s.path.end_color w.adjacent_endpoint
  have hm := map_mono (f := (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom) h
  rw [map_commutator, ← Z_act, ← Q_act, ← U_act,
    show act R g s.endpoint = s.endpoint from g.property] at hm
  exact hm

/-- V0 centralizes the endpoint kernel plane inside the elementary radius group. -/
theorem span_centralizes_kernel (hb : 4 < geometry.b R) :
    s.continuationSpan w ≤ centralizer
      (U R s.endpoint ⊓ Q R s.start : Set (FreeAmalgam R)) := by
  let := V_abelian_of_four_lt R s.path.end_color hb
  exact (w.span_le_radius (by omega)).trans
    ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le (inf_le_left.trans ((U_le_Z R s.endpoint).trans (Z_le_VBall R s.endpoint 2)))))

private theorem center_Z_le_start_kernel (hb : 4 < geometry.b R) : Z R s.center ≤ Q R s.start := by
  apply Z_le_Q_of_dist_lt R s.center (geometry.exists_critical s.center (s.center_color (by omega)))
  rw [geometry.distance_constant s.center (s.center_color (by omega)), SimpleGraph.dist_comm,
    s.center_distance (by omega)]
  change 2 < geometry.b R
  omega

private theorem center_Z_le_endpoint_kernel (hb : 2 ≤ geometry.b R) :
    Z R s.center ≤ Q R s.endpoint := by
  apply Z_le_Q_of_dist_lt R s.center (geometry.exists_critical s.center (s.center_color hb))
  rw [geometry.distance_constant s.center (s.center_color hb), s.path.dist_end, s.path.length_eq_b]
  change geometry.b R - 2 < geometry.b R
  omega

/-- Upper bound for the center displacement of the entire orbit span. -/
theorem center_commutator_le_kernel [Finite M] (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) :
    ⁅Z R s.center, s.continuationSpan w⁆ ≤ U R s.endpoint ⊓ Q R s.start := by
  rw [commutator_comm]
  have hn := (w.span_centralizes_kernel hb).trans (centralizer_le_normalizer _)
  apply (commutator_mono (K₂ := Z R s.center) ?_ le_rfl).trans
    (commutator_commutatorPreimage_le (s.continuationSpan w) (Z R s.center)
      (U R s.endpoint ⊓ Q R s.start) hn)
  change (⨆ g : stabilizer R s.endpoint, Z R (act R g w.vertex)) ≤ _
  apply iSup_le
  intro g
  apply le_commutatorPreimage (le_iSup _ g)
  apply le_inf
  · exact (commutator_mono le_rfl (center_Z_le_endpoint_kernel (s := s) (by omega))).trans
      (w.orbit_displacement_le_U common (by omega) g)
  · exact (le_normalizer_iff_commutator_le_right.mp
      ((w.orbit_Z_le_center_stabilizer (by omega) g).trans (Z_normalized R s.center))).trans
        (center_Z_le_start_kernel (s := s) hb)

/-- Every avoiding line occurs in the center displacement of any chosen V0. -/
theorem endpointSpan_le_center_commutator :
    s.endpointSpan ≤ ⁅Z R s.center, s.continuationSpan w⁆ := by
  apply iSup_le
  intro w'
  apply commutator_mono le_rfl
  have hz := Z_le_localZSpan R w'.vertex s.endpoint
  change Z R w'.vertex ≤ s.continuationSpan w' at hz
  rw [w'.span_eq w] at hz
  exact hz

/-- With the generated-plane identity, the actual center displacement is that plane. -/
theorem center_commutator_eq_of_generated [Finite M] (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R)
    (hgen : s.endpointSpan = U R s.endpoint ⊓ Q R s.start) :
    ⁅Z R s.center, s.continuationSpan w⁆ = s.endpointSpan := by
  exact le_antisymm ((w.center_commutator_le_kernel common hb).trans hgen.ge)
    w.endpointSpan_le_center_commutator

/-- The radius/kernel intersection has the required commutator bound before
identifying the span generated by the avoiding lines. -/
theorem radius_commutator_le_kernel [Finite M] (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) :
    ⁅V R s.center ⊓ Q R s.endpoint, s.continuationSpan w⁆ ≤ U R s.endpoint ⊓ Q R s.start := by
  rw [commutator_comm]
  have hn := (w.span_centralizes_kernel hb).trans (centralizer_le_normalizer _)
  apply (commutator_mono (K₂ := V R s.center ⊓ Q R s.endpoint) ?_ le_rfl).trans
    (commutator_commutatorPreimage_le (s.continuationSpan w) (V R s.center ⊓ Q R s.endpoint)
      (U R s.endpoint ⊓ Q R s.start) hn)
  change (⨆ g : stabilizer R s.endpoint, Z R (act R g w.vertex)) ≤ _
  apply iSup_le
  intro g
  apply le_commutatorPreimage (le_iSup _ g)
  apply le_inf
  · exact (commutator_mono le_rfl inf_le_right).trans
      (w.orbit_displacement_le_U common (by omega) g)
  · apply ((commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp
        ((w.orbit_Z_le_center_stabilizer (by omega) g).trans (V_normalized R s.center)))).trans
    apply V_le_Q_of_dist_add_two_lt R (s.center_color (by omega))
    rw [SimpleGraph.dist_comm, s.center_distance (by omega)]
    exact hb

/-- The literal ForwardFacts radius bound, conditional only on generation. -/
theorem radius_commutator_of_generated [Finite M] (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R)
    (hgen : s.endpointSpan = U R s.endpoint ⊓ Q R s.start) :
    ⁅V R s.center ⊓ Q R s.endpoint, s.continuationSpan w⁆ ≤ s.endpointSpan :=
  (w.radius_commutator_le_kernel common hb).trans hgen.ge

end Continuation
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.SelectedPath
