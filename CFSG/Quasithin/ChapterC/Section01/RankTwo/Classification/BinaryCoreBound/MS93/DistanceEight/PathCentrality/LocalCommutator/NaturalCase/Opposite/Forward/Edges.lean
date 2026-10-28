module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Forward.Orbit
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.OrderTwo.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.OrderTwo.Generation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.CriticalCriterion
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Sharpening.Source

/-!
# Full edge planes for the selected forward continuations

An order-two edge supplies all hypotheses of source (2.3), including the
proved local conjugate-generation and critical-witness bounds. Its conclusion
b = 4 contradicts b > 4. Thus the selected edge and every transported edge
have order four. The given cyclic displacement sandwiches the full [Z_a,Q_c],
and uniqueness of the tree midpoint identifies the transported edge literally.
No later distance-four exclusion or escape counterexample is used.

Source: Meierfrankenfeld--Stellmacher (1993), (2.3), pp.857--859,
and (4.4.1)(1), printed p.891.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.SelectedPath
variable {M : Type*} [Group M] {L R : Subgroup M}
variable {source : LocalSource L R} {geometry : Geometry R}
variable {a c : Vertex R} (s : SelectedPath R geometry a c)

/-- Source (2.3) excludes an order-two edge at distance greater than four. -/
theorem edge_card [Finite M] (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) : Nat.card s.edge = 4 := by
  rcases Escape.EdgeTransfer.Sharpening.edge_displacement_card_two_or_four
    common.large_distance (moduleFacts common) s.start s.first s.path.start_color
    (s.adjacent_first (by omega)) with htwo | hfour
  · have hcomm : CriticalCriterion.CommutatorControl R geometry := by
      intro d hd d' hcrit
      obtain ⟨hle, hnot, hbound⟩ := DistanceFour.Early.OrderTwo.critical_witness_bound
        common s.start s.first s.path.start_color (s.adjacent_first (by omega))
        htwo d d' hd hcrit
      exact ⟨Z R d', hle, hnot, fun t ht Y hY _ => hbound t ht.1 ht.2 Y hY⟩
    obtain ⟨hle, hn, hnot, hbound⟩ := DistanceFour.Early.OrderTwo.edge_source_d
      common s.start s.first s.path.start_color (s.adjacent_first (by omega)) htwo
    have hA : CriticalCriterion.EdgeWitness R geometry s.start s.first s.edge := by
      refine ⟨hle, hn, hnot, ?_⟩
      intro ha' d hd hpath
      apply hbound d hd
      rwa [hd.1, geometry.distance_constant s.start ha']
    have hpath : (cosetGraph R).dist s.center s.endpoint + 2 =
        (cosetGraph R).dist s.start s.endpoint := by
      have hd := s.path.dist_end 2
      rw [s.path.length_eq_b] at hd
      have he := s.path.shortest.symm.trans s.path.length_eq_b
      change (cosetGraph R).dist s.center s.endpoint = geometry.b R - 2 at hd
      omega
    have hfour := (source_2_3 source geometry (by omega) s.start s.path.start_color
      s.endpoint s.path.critical s.first s.center (s.adjacent_first (by omega))
      (s.adjacent_center_first (by omega)) (s.center_distance (by omega)) hpath
      (DistanceFour.Early.OrderTwo.edge_element_conjugate_generation source s.start
        s.first s.path.start_color (s.adjacent_first (by omega))) hcomm s.edge hA).1
    omega
  · exact hfour

/-- The cyclic displacement in the selection determines the full displacement. -/
theorem displacement_eq_edge [Finite M] (hb : 2 ≤ geometry.b R) :
    ⁅Z R s.start, Q R s.center⁆ = s.edge := by
  apply le_antisymm
  · apply commutator_mono le_rfl
    apply Q_le_adjacent_h R _ (s.adjacent_center_first hb)
    have hh := adjacent_color_ne R (s.adjacent_first hb)
    cases hc : color R s.first <;> simp_all [s.path.start_color]
  · change edgeCommutator R s.start s.first ≤ _
    rw [← s.displacement]
    exact commutator_mono (zpowers_le.mpr s.element_mem) le_rfl

namespace Continuation
variable {s} (w : s.Continuation)

/-- The continuation conjugator carries the original first vertex to its actual midpoint. -/
theorem first_image (hb : 2 ≤ geometry.b R) :
    act R w.conjugator s.first = w.intermediate := by
  let u : (cosetGraph R).Walk w.vertex s.endpoint :=
    .cons ((cosetGraph_adj R _ _).mpr (by
      rw [← w.start_image]
      exact (adjacent_act_iff R _ _ _).mpr (s.adjacent_first hb)))
      (.cons ((cosetGraph_adj R _ _).mpr (by
        rw [← w.center_image]
        exact (adjacent_act_iff R _ _ _).mpr (adjacent_symm R (s.adjacent_center_first hb)))) .nil)
  let v : (cosetGraph R).Walk w.vertex s.endpoint :=
    .cons ((cosetGraph_adj R _ _).mpr (adjacent_symm R w.adjacent_vertex))
      (.cons ((cosetGraph_adj R _ _).mpr (adjacent_symm R w.adjacent_endpoint)) .nil)
  have hu : u.length = (cosetGraph R).dist w.vertex s.endpoint :=
    (w.endpoint_distance hb).symm
  have hv : v.length = (cosetGraph R).dist w.vertex s.endpoint :=
    (w.endpoint_distance hb).symm
  have hh := (geometry.tree.isAcyclic.subsingleton_path w.vertex s.endpoint).elim
    ⟨u, u.isPath_of_length_eq_dist hu⟩ ⟨v, v.isPath_of_length_eq_dist hv⟩
  exact congrArg (fun p : (cosetGraph R).Path w.vertex s.endpoint => p.val.getVert 1) hh

/-- Both sides of the selected edge identity transport to the prescribed continuation edge. -/
theorem edge_eq (hb : 2 ≤ geometry.b R) :
    edgeCommutator R w.vertex w.intermediate =
      edgeCommutator R s.endpoint w.intermediate := by
  have hh := congrArg (Subgroup.map (MulAut.conj w.conjugator⁻¹).toMonoidHom) s.edge_eq
  rw [← edge_act, ← edge_act] at hh
  simpa only [w.start_image, w.center_image, w.first_image hb] using hh

/-- Transport of the full initial displacement, with the actual kernel at the endpoint. -/
theorem displacement_eq_edge [Finite M] (hb : 2 ≤ geometry.b R) :
    ⁅Z R w.vertex, Q R s.endpoint⁆ = edgeCommutator R s.endpoint w.intermediate := by
  have hh := congrArg (Subgroup.map (MulAut.conj w.conjugator⁻¹).toMonoidHom)
    (s.displacement_eq_edge hb)
  change _ = (edgeCommutator R s.start s.first).map _ at hh
  rw [map_commutator, ← Z_act, ← Q_act, ← edge_act] at hh
  simpa only [w.start_image, w.center_image, w.first_image hb, w.edge_eq hb] using hh

/-- Every retained continuation edge is a plane in the endpoint natural module. -/
theorem edge_card [Finite M] (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) :
    Nat.card (edgeCommutator R s.endpoint w.intermediate) = 4 := by
  exact (DistanceFour.Early.OrderTwo.edge_card_eq s.endpoint w.intermediate s.start s.first
    s.path.end_color s.path.start_color w.adjacent_endpoint (s.adjacent_first (by omega))).trans
      (s.edge_card common hb)

end Continuation
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.SelectedPath
