module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicLocalGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.CriticalActorApplication

/-!
# Intrinsic setup for the noncommuting epsilon-one branch

The full edge core, the actual Sylow-generated local actors and the
unconditional adjacent-core obstruction supply the hypotheses of the
existing Chapter 7 radius-one argument. This proves its distance bound
without recognizing the actor on the opposite vertex orbit, even when
an original PSU₃(2) quotient permits a strict enlargement.

Consequently a hypothetical noncommuting pair with b > 2 has the exact
central seed at every neighbor of either critical endpoint, and its two
endpoints lie in the same orbit at even distance. These facts prepare the
literal long-branch radius action in `IntrinsicRadiusAction`. They do not
assume b=2 or settle the remaining long-distance contradiction.

Source: DGS, *Groups and Graphs* (1985), 6.2, 6.6 and 7.3--7.4,
pp.119,123,127--128. All graph cores and the full edge stabilizer are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open Noncommuting
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))

/-- All earlier local premises of the existing epsilon-one bound are discharged. -/
theorem reduced_intrinsic_epsilonOne_bound (h : HypothesisF11 L S)
    {v w u : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hvu : (graph F).Adj v u)
    (hepsilon : Z F u ≠ omegaCenterIn ((stabilizer F v ⊓ stabilizer F u).pCoreIn 2)) :
    b F = 1 ∨ b F = 2 := by
  let ht := reduced_triple h
  let := finite_endpoints ht
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let : IsElementaryAbelian 2 (Z F w) := graph_Z_elementary ht w
  have hother : Z F w ≤ graphLocalGroup F v :=
    pGroup_le_sylowGenerated _ _ (criticalPair_centers F ht.generate hc).1
      (IsElementaryAbelian.isPGroup 2 _)
  have hnc : Z F u ≠ omegaCenterIn (graphLocalGroup F u) := by
    intro hh
    apply hepsilon
    simpa only [reducedFamily,inf_comm] using
      (graph_intrinsic_seed_eq_iff ht (reduced_borel_core_sylow h)
        (reduced_vertex_sylow h) hvu.symm).mpr hh
  have hCS := graph_sylow_centralizers_of_epsilonOne ht (graphLocalGroup F)
    (graphLocalGroup_conjugate ht)
    (graph_intrinsic_centralizer_dichotomy ht (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h)) hvu hnc hother hne
  have hobs : ∀ x y, (graph F).Adj x y → ¬ stabilizer F x ≤
      normalizer ((Z F y ⊔ Z F x : Subgroup (G₀ L S)) : Set (G₀ L S)) := by
    intro x y he hn
    have hs := (reduced_graph_center_product h he.symm hn).1
    obtain ⟨T,hT⟩ := source_edge_vertex_sylow ht (reduced_vertex_sylow h) he.symm
    have hTe := sylow_image_eq_edge_core (stabilizer F y)
      (stabilizer F y ⊓ stabilizer F x) inf_le_left
      (source_edge_core_sylow ht (reduced_borel_core_sylow h) he.symm) T hT
    exact graph_intrinsic_seed_ne_of_centralizerSylow ht (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) he.symm (hCS y) ((hs T).trans (congrArg omegaCenterIn hTe))
  have hb := graph_radiusOne_distance_bound ht (reduced_kernel_sylow h)
    (graphLocalGroup F) (fun _ => sylowGenerated_le _)
    (fun _ _ he => graph_intrinsic_edge_factor ht (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) he)
    (fun _ _ _ => graph_intrinsic_edgeCore_le ht)
    (fun _ _ he => graph_intrinsic_escaping_twoGroup_generates ht
      (reduced_borel_core_sylow h) (reduced_vertex_sylow h) he)
    (fun x y hc hne => (reduced_critical_natural_centers_and_products h hc hne).2.2.2.1)
    hobs hCS hc hne
  have hp := source_b_positive ht
  change b F ≤ 2 at hb
  change 0 < b F at hp
  omega

/-- A long critical pair forces the literal central seed at each adjacent vertex. -/
theorem reduced_long_critical_neighbor_seed (h : HypothesisF11 L S)
    {v w u : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : 2 < b F) (hvu : (graph F).Adj v u) :
    Z F u = omegaCenterIn ((stabilizer F v ⊓ stabilizer F u).pCoreIn 2) ∧
      Z F u = omegaCenterIn (graphLocalGroup F u) := by
  have hs : Z F u = omegaCenterIn ((stabilizer F v ⊓ stabilizer F u).pCoreIn 2) := by
    by_contra hh
    rcases reduced_intrinsic_epsilonOne_bound h hc hne hvu hh with hb' | hb' <;> omega
  refine ⟨hs,?_⟩
  apply (graph_intrinsic_seed_eq_iff (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hvu.symm).mp
  simpa only [reducedFamily,inf_comm] using hs

/-- The long noncommuting branch lies in one vertex orbit and has even distance. -/
theorem reduced_long_critical_even (h : HypothesisF11 L S)
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : 2 < b F) : (∃ g : G₀ L S, g • v = w) ∧ Even (b F) := by
  let ht := reduced_triple h
  let := finite_endpoints ht
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let : IsElementaryAbelian 2 (Z F v) := graph_Z_elementary ht v
  have hvw : w ≠ v := by
    intro hh
    have hd := hc.1
    rw [hh,SimpleGraph.dist_self] at hd
    omega
  obtain ⟨u,hvu,_⟩ := exists_predecessor F ht.generate w v hvw
  have hother : Z F v ≤ graphLocalGroup F w :=
    pGroup_le_sylowGenerated _ _ (Z_le_stabilizer_of_dist_le_b F ht.generate v w hc.1.le)
      (IsElementaryAbelian.isPGroup 2 _)
  exact graph_even_of_epsilonTwo ht (graphLocalGroup F) (graphLocalGroup_conjugate ht)
    hc hvu (reduced_long_critical_neighbor_seed h hc hne hb hvu).2 hother hne
end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
