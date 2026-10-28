module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.LocalAction

/-!
# The actual avoiding ordered-pair orbit on MS93 p.891

Irreducibility of the marked natural subgroup makes the intersection of all
incident edge displacements trivial. Thus some edge avoids the nonzero critical
line. Local edge transitivity fills it by a conjugate of the original ordered
pair, retaining the conjugator and both adjacency witnesses. The continuation
has the source distance bound; criticality is proved separately.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)(1), printed p.891.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite
variable {M : Type*} [Group M] {L R : Subgroup M}
variable {source : LocalSource L R} {geometry : Geometry R}

theorem edge_act (g : FreeAmalgam R) (a t : Vertex R) :
    edgeCommutator R (act R g a) (act R g t) =
      (edgeCommutator R a t).map (MulAut.conj g⁻¹).toMonoidHom := by
  simp only [edgeCommutator, Z_act, Q_act, map_commutator]

private theorem edge_normal_subgroup_eq_bot [Finite M]
    (common : CommonFacts R source geometry) {a t : Vertex R}
    (ha : color R a = false) (hat : Adjacent R a t)
    (K : Subgroup (FreeAmalgam R)) (hK : K ≤ edgeCommutator R a t)
    (hn : stabilizer R a ≤ normalizer (K : Set (FreeAmalgam R))) : K = ⊥ := by
  obtain ⟨model⟩ := Escape.Propagation.Backward.Products.Selection.Choices.localModel_nonempty
    source (moduleFacts common) a ha
  obtain ⟨n⟩ := Escape.PairingControl.FirstPairing.Orientation.naturalU_nonempty
    (moduleFacts common) a ha model.projection model.surjective model.kernel
  have hEU := Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
    (moduleFacts common) a t ha hat
  have hKU := hK.trans hEU
  have hUG := (U_le_Z R a).trans (Z_le_stabilizer R a)
  have hKG := hKU.trans hUG
  let : (K.subgroupOf (stabilizer R a)).Normal := normal_subgroupOf_of_le_normalizer hn
  have him : (⊤ : Subgroup (stabilizer R a)).map model.projection = ⊤ := by
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr model.surjective
  rcases n.irreducible him (K.subgroupOf (stabilizer R a))
    (fun _ hx => hKU hx) le_normalizer_of_normal with h | h
  · have hh := congrArg (Subgroup.map (stabilizer R a).subtype) h
    simpa only [map_subgroupOf_eq_of_le hKG, Subgroup.map_bot] using hh
  · have hh := congrArg (Subgroup.map (stabilizer R a).subtype) h
    have heq : K = U R a := by
      simpa only [map_subgroupOf_eq_of_le hKG, map_subgroupOf_eq_of_le hUG] using hh
    have hUedge : U R a ≤ edgeCommutator R a t := heq ▸ hK
    let := finite_stabilizer R a
    let : Finite (edgeCommutator R a t) := Finite.of_injective
      (inclusion (hEU.trans hUG)) (inclusion_injective _)
    have hcard := Nat.card_le_card_of_injective (inclusion hUedge) (inclusion_injective _)
    have hsmall := Escape.EdgeTransfer.edge_displacement_card_le_four
      common.large_distance (moduleFacts common) a t ha hat
    rw [common.natural.card_at a ha] at hcard
    change Nat.card (edgeCommutator R a t) ≤ 4 at hsmall
    omega

/-- Irreducibility makes some actual edge omit every prescribed nonzero group. -/
theorem exists_avoiding_edge [Finite M] (common : CommonFacts R source geometry)
    {a : Vertex R} (ha : color R a = false)
    (K : Subgroup (FreeAmalgam R)) (hne : K ≠ ⊥) :
    ∃ t, Adjacent R a t ∧ ¬ K ≤ edgeCommutator R a t := by
  classical
  let J : Subgroup (FreeAmalgam R) := ⨅ t, ⨅ (_ : Adjacent R a t), edgeCommutator R a t
  have hJ : ∀ t, Adjacent R a t → J ≤ edgeCommutator R a t :=
    fun t ht => (iInf_le _ t).trans (iInf_le _ ht)
  have hn : stabilizer R a ≤ normalizer (J : Set (FreeAmalgam R)) := by
    apply le_normalizer_iff.mpr
    intro g hg x hx
    apply mem_iInf.mpr
    intro t
    apply mem_iInf.mpr
    intro ht
    have hga : act R g a = a := hg
    have hgai : act R g⁻¹ a = a := (stabilizer R a).inv_mem hg
    have hgt : Adjacent R a (act R g t) := by
      rw [← hga]
      exact (adjacent_act_iff R g a t).mpr ht
    have hx' := mem_map_of_mem (MulAut.conj g).toMonoidHom (hJ _ hgt hx)
    have he := edge_act g⁻¹ a (act R g t)
    simp only [hgai, ← act_mul, mul_inv_cancel, act_one, inv_inv] at he
    rwa [← he] at hx'
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  have hadj : Adjacent R (mVertex R g) (hVertex R g) := by
    simpa only [act_mVertex, act_hVertex, one_mul] using
      (adjacent_act_iff R g (mVertex R 1) (hVertex R 1)).mpr (base_adjacent R)
  have hzero := edge_normal_subgroup_eq_bot common
    (show color R (mVertex R g) = false from rfl) hadj J (hJ _ hadj) hn
  by_contra! h
  apply hne
  apply le_bot_iff.mp
  rw [← hzero]
  exact le_iInf fun t => le_iInf fun ht => h t ht

namespace SelectedPath
variable {a c : Vertex R} (s : SelectedPath R geometry a c)

theorem adjacent_first (hb : 2 ≤ geometry.b R) :
    Adjacent R s.start s.first := by
  apply (cosetGraph_adj R _ _).mp
  simpa using s.path.walk.adj_getVert_succ (i := 0)
    (by rw [s.path.length_eq_b]; omega)

theorem adjacent_center_first (hb : 2 ≤ geometry.b R) :
    Adjacent R s.center s.first :=
  adjacent_symm R ((cosetGraph_adj R _ _).mp
    (s.path.walk.adj_getVert_succ (i := 1) (by rw [s.path.length_eq_b]; omega)))

/-- Every avoiding incident edge can be filled in the prescribed ordered-pair orbit. -/
theorem continuation_at [Finite M] (hb : 2 ≤ geometry.b R) {t : Vertex R}
    (ht : Adjacent R s.endpoint t) (havoid : ¬ s.criticalLine ≤ edgeCommutator R s.endpoint t) :
    ∃ w : s.Continuation, w.intermediate = t := by
  obtain ⟨g, hg⟩ := exists_mVertex_of_color R (s.center_color hb)
  obtain ⟨h, hh⟩ := exists_mVertex_of_color R s.path.end_color
  have hmove : act R (g⁻¹ * h) s.center = s.endpoint := by
    rw [hg, act_mVertex, mul_inv_cancel_left, hh]
  have hfirst : Adjacent R s.endpoint (act R (g⁻¹ * h) s.first) := by
    rw [← hmove]
    exact (adjacent_act_iff R _ _ _).mpr (s.adjacent_center_first hb)
  obtain ⟨k, hk, hkt⟩ := stabilizer_transitive_neighbors R s.endpoint hfirst ht
  have hkfix : act R k s.endpoint = s.endpoint := hk
  let f := (g⁻¹ * h) * k
  have hf : act R f s.first = t := by rw [act_mul]; exact hkt
  refine ⟨{
    intermediate := t
    vertex := act R f s.start
    adjacent_endpoint := ht
    adjacent_vertex := ?_
    conjugator := f
    start_image := rfl
    center_image := ?_
    avoidance := havoid }, rfl⟩
  · rw [← hf]
    exact (adjacent_act_iff R _ _ _).mpr (adjacent_symm R (s.adjacent_first hb))
  · rw [act_mul, hmove, hkfix]

/-- The first field of ForwardFacts, with the complete orbit witness retained. -/
theorem continuation_exists [Finite M] (common : CommonFacts R source geometry)
    (hb : 2 ≤ geometry.b R) : Nonempty s.Continuation := by
  obtain ⟨t, ht, havoid⟩ := exists_avoiding_edge common s.path.end_color s.criticalLine
    (common.critical_noncommutation s.start s.path.start_color s.endpoint s.path.critical)
  obtain ⟨w, _⟩ := s.continuation_at hb ht havoid
  exact ⟨w⟩

namespace Continuation
variable {s} (w : s.Continuation)

theorem vertex_color : color R w.vertex = false := by
  rw [← w.start_image, action_preserves_color]
  exact s.path.start_color

theorem endpoint_distance (hb : 2 ≤ geometry.b R) :
    (cosetGraph R).dist w.vertex s.endpoint = 2 := by
  rw [← w.start_image, ← w.center_image, dist_act]
  exact s.center_distance hb

theorem span_le_radius (hb : 2 ≤ geometry.b R) : s.continuationSpan w ≤ V R s.endpoint :=
  localZSpan_le_V R (w.endpoint_distance hb).le

theorem center_distance_le (hb : 2 ≤ geometry.b R) :
    (cosetGraph R).dist s.center w.vertex ≤ geometry.b R := by
  have htri := (cosetGraph_connected R).dist_triangle
    (u := s.center) (v := s.endpoint) (w := w.vertex)
  rw [SimpleGraph.dist_comm (u := s.endpoint), w.endpoint_distance hb] at htri
  have hd := s.path.dist_end 2
  rw [s.path.length_eq_b] at hd
  change (cosetGraph R).dist s.center s.endpoint = geometry.b R - 2 at hd
  omega

theorem critical_iff (hb : 2 ≤ geometry.b R) :
    CriticalPair R s.center w.vertex (geometry.exists_critical s.center (s.center_color hb)) ↔
      ¬ Z R s.center ≤ Q R w.vertex := by
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have hmin := criticalDistance_le R s.center
    (geometry.exists_critical s.center (s.center_color hb)) h
  rw [geometry.distance_constant s.center (s.center_color hb)] at hmin ⊢
  exact le_antisymm (w.center_distance_le hb) hmin

end Continuation
end SelectedPath
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite
