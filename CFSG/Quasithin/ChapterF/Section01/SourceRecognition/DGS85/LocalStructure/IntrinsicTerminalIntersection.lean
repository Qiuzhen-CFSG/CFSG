module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicRadiusAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.IntersectionIndex

/-!
# Intrinsic normality of the terminal radius/core intersection

The proved natural critical action and the full adjacent-core obstruction
identify the neighbor commutator at every neighbor, without recognizing the
opposite actor. For K = V_a intersect Q_t, the full critical Sylow product
then makes K invariant under both Q_a and Z_w. The existing root-and-mover
transitivity theorem and radius transport apply to these exact groups.

This removes the global actor catalogue from the intersection-normality
step in DGS (7.5). The final mover and centralizer comparisons remain
geometric obligations, not assumed representation data.
Source: DGS, *Groups and Graphs* (1985), (7.4)(d) and (7.5), pp.128--131.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open Noncommuting
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))

/-- Every neighbor supplies the exact natural-center and radius commutators. -/
theorem reduced_long_neighbor_radius_commutator (h : HypothesisF11 L S)
    {v w a : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : 2 < b F) (hva : (graph F).Adj v a) :
    Z F a ≤ Z F v ∧ ⁅Z F v,Q F a⁆ = Z F a ∧ ⁅V F a 1,Q F a⁆ = Z F a := by
  let ht := reduced_triple h
  let := finite_endpoints ht
  let : ∀ i, Finite (F i) := finite_endpoints ht
  obtain ⟨c,hcL⟩ := reduced_critical_actor_localData h hc hne hva
  change c.Pstar = graphLocalGroup F v at hcL
  have ho : ¬ 2 ∣ c.Pstar.relIndex (stabilizer F v) := by
    rw [hcL]
    exact graph_actor_odd_index ht v
  have hseed := (reduced_long_critical_neighbor_seed h hc hne hb hva).1
  have hcenter : center c.Pstar = ⊥ := by
    rw [hcL]
    exact reduced_long_critical_center_trivial h hc hne hb hva
  have hnat : HasNaturalCenter c.Pstar (Z F v) (Q F v) := by
    rw [hcL]
    exact (reduced_critical_natural_centers_and_products h hc hne).1
  have hQS : Q F a ≤ (stabilizer F v ⊓ stabilizer F a).pCoreIn 2 := by
    simpa only [inf_comm] using graph_Q_le_edgeCore ht hva.symm
  have hesc : ¬ Q F a ≤ Q F v := by
    intro hh
    apply reduced_graph_core_obstruction h a v hva.symm
    dsimp only [reducedFamily]
    rw [inf_eq_right.mpr hh]
    exact (stabilizer F a).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hQ := (graph_natural_edge_commutator ht (reduced_borel_core_sylow h)
    hva c ho hcenter hnat (Q F a) hQS hesc).trans hseed.symm
  exact ⟨hseed.le.trans (graph_edgeSeed_le_Z ht (reduced_borel_core_sylow h) hva c ho),
    hQ,graph_radius_one_commutator_of_edge ht hva hQ⟩

/-- The actual radius/core intersection is normalized by the two source generators. -/
theorem reduced_long_radius_core_intersection_normalized (h : HypothesisF11 L S)
    {v w a t : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : 2 < b F) (hva : (graph F).Adj v a) (hwt : (graph F).Adj w t)
    (hdt : (graph F).dist v t + 1 = b F) :
    Q F a ⊔ Z F w ≤ normalizer ((V F a 1 ⊓ Q F t : Subgroup (G₀ L S)) : Set (G₀ L S)) := by
  let ht := reduced_triple h
  let := finite_endpoints ht
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let A := V F a 1
  let K := A ⊓ Q F t
  have hAv : A ≤ stabilizer F v :=
    graph_V_le_stabilizer_of_distance ht (by rw [SimpleGraph.dist_comm,
      SimpleGraph.dist_eq_one_iff_adj.mpr hva]; omega)
  have hZWv : Z F w ≤ stabilizer F v :=
    Z_le_stabilizer_of_dist_le_b F ht.generate w v (by rw [SimpleGraph.dist_comm,hc.1])
  have hZvA : Z F v ≤ A :=
    le_iSup_of_le v (le_iSup_of_le ((mem_ball_one _ _ _).mpr (Or.inl hva.symm)) le_rfl)
  have hZvK : Z F v ≤ K := le_inf hZvA
    (graph_Z_le_Q_of_short ht (reduced_kernel_sylow h) (by omega))
  have hcomm := reduced_long_neighbor_radius_commutator h hc hne hb hva
  have hQaK : Q F a ≤ normalizer (K : Set (G₀ L S)) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact ((commutator_mono inf_le_left le_rfl).trans hcomm.2.2.le).trans
      (hcomm.1.trans hZvK)
  have hZvN : stabilizer F v ≤ normalizer (Z F v : Set (G₀ L S)) :=
    (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F v)).mp (Z_normal F v)
  have hZwN : stabilizer F w ≤ normalizer (Z F w : Set (G₀ L S)) :=
    (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F w)).mp (Z_normal F w)
  have hZvZw : Z F v ≤ normalizer (Z F w : Set (G₀ L S)) :=
    (Z_le_stabilizer_of_dist_le_b F ht.generate v w hc.1.le).trans hZwN
  have hKw : K ≤ stabilizer F w :=
    (inf_le_right.trans (source_Z_Q_U ht t).2).trans
      ((ballKernel_one_le_edge F hwt.symm).trans inf_le_right)
  have hRK : ⁅Z F v,Z F w⁆ ≤ K :=
    (le_normalizer_iff_commutator_le_left.mp (hZWv.trans hZvN)).trans hZvK
  have hsyl := (reduced_critical_natural_centers_and_products h hc hne).2.2.2.1
  have hZwK : Z F w ≤ normalizer (K : Set (G₀ L S)) :=
    (source_radius_commutator (stabilizer F w) (Z F v) (Z F w) K
      ((graph_V_isPGroup_of_short ht (reduced_kernel_sylow h) a
        (by omega : 1 < b F)).to_le inf_le_left)
      ((inf_le_left.trans hAv).trans hZvN) hZvK hKw hZvZw
      (graph_Q_centralizes_Z ht w) hsyl).2.2 K hRK le_rfl
  exact sup_le hQaK hZwK

/-- Apply the existing root-and-mover action to the now-proved normality premise. -/
theorem reduced_long_radius_core_intersection_le_neighbors (h : HypothesisF11 L S)
    {v w a t : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : 2 < b F) (hva : (graph F).Adj v a) (hwt : (graph F).Adj w t)
    (hdt : (graph F).dist v t + 1 = b F)
    (hm : ∃ g ∈ Z F w, g • a ≠ a) :
    ∀ x, (graph F).Adj v x → V F a 1 ⊓ Q F t ≤ V F x 1 := by
  let ht := reduced_triple h
  let := finite_endpoints ht
  let : ∀ i, Finite (F i) := finite_endpoints ht
  obtain ⟨c,hcL⟩ := reduced_critical_actor_localData h hc hne hva
  change c.Pstar = graphLocalGroup F v at hcL
  have ho : ¬ 2 ∣ c.Pstar.relIndex (stabilizer F v) := by
    rw [hcL]
    exact graph_actor_odd_index ht v
  have hnat : HasNaturalCenter c.Pstar (Z F v) (Q F v) := by
    rw [hcL]
    exact (reduced_critical_natural_centers_and_products h hc hne).1
  apply graph_normalized_radius_intersection_le_neighbors ht
    (Q F a ⊔ Z F w) (V F a 1 ⊓ Q F t) inf_le_left
    (reduced_long_radius_core_intersection_normalized h hc hne hb hva hwt hdt)
  intro x hx
  exact graph_core_and_mover_transitive ht (reduced_borel_core_sylow h) hva c ho hnat
    (reduced_graph_core_obstruction h a v hva.symm) (Z F w)
    (Z_le_stabilizer_of_dist_le_b F ht.generate w v (by rw [SimpleGraph.dist_comm,hc.1])) hm hx

end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
