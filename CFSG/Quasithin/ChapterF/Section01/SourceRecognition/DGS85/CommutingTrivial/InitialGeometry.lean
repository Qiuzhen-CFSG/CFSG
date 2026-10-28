module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.LocalActor
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.Source
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.KernelControl

/-!
# The opening Chapter 9 clauses for the intrinsic local groups

A common edge Sylow puts the central omega of one local actor in the
opposite center span. If that opposite span is central in its local actor,
both locally transitive groups normalize the first omega. Faithfulness
forces it to vanish, and characteristic two then kills the full center.

This specializes the Chapter 8 normalizer argument to the constructed
intrinsic local groups. It does not assume the separate 6.5 obstruction.
The reduced critical application discharges common Sylows, transitivity,
centrality of the opposite span and the kernel-Sylow premise, and includes
the original elementary spans, quadratic actions and forward centralizer.

Source: DGS, *Groups and Graphs* (1985), 8.1(b), pp.132--133, and
9.1--9.3, pp.141--142. The terminal distance and field bounds remain open.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
/-- A common edge Sylow puts local central omega in the opposite center span. -/
theorem intrinsic_local_omega_le_neighbor_Z (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w) :
    omegaCenterIn (graphLocalGroup (family P) v) ≤ Z (family P) w := by
  obtain ⟨T, T', hTT⟩ := source_common_edge_sylow h hB hS hvw
  have hcentral : omegaCenterIn (graphLocalGroup (family P) v) ≤ centralizer (graphLocalGroup (family P) v : Set G) :=
    fun x hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1
  have hT : omegaCenterIn (graphLocalGroup (family P) v) ≤
      (T : Subgroup (stabilizer (family P) v)).map (stabilizer (family P) v).subtype :=
    le_sylow_image_of_normalizes _ T rfl (IsElementaryAbelian.isPGroup 2 _)
      ((map_subtype_le _).trans (sylowGenerated_le _))
      ((hcentral.trans (centralizer_le (sylow_le_sylowGenerated _ T))).trans
        (Subgroup.centralizer_le_normalizer _))
  have hΩ : omegaCenterIn (graphLocalGroup (family P) v) ≤ omegaCenterIn
      ((T : Subgroup (stabilizer (family P) v)).map (stabilizer (family P) v).subtype) := by
    intro x hx
    exact (mem_omegaCenterIn_iff _ _).mpr ⟨hT hx,
      centralizer_le (sylow_le_sylowGenerated _ T) (hcentral hx),
      ((mem_omegaCenterIn_iff _ _).mp hx).2.2⟩
  rw [hTT] at hΩ
  exact hΩ.trans (le_iSup (fun R : Sylow 2 (stabilizer (family P) w) =>
    omegaCenterIn ((R : Subgroup (stabilizer (family P) w)).map
      (stabilizer (family P) w).subtype)) T')

/-- The local transitive-normalizer argument kills the starting central omega. -/
theorem intrinsic_local_omega_eq_bot_of_neighbor_central (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hZ : Z (family P) w = omegaCenterIn (graphLocalGroup (family P) w)) :
    omegaCenterIn (graphLocalGroup (family P) v) = ⊥ := by
  have hneighbor := intrinsic_local_omega_le_neighbor_Z h hB hS hvw
  have hnv : graphLocalGroup (family P) v ≤ normalizer (omegaCenterIn (graphLocalGroup (family P) v) : Set G) :=
    (graphLocalGroup (family P) v).le_normalizer.trans (normalizer_le_normalizer_omegaCenterIn _)
  have hnw : graphLocalGroup (family P) w ≤ normalizer (omegaCenterIn (graphLocalGroup (family P) v) : Set G) := by
    apply (le_centralizer_iff.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
    intro x hx
    exact ((mem_omegaCenterIn_iff _ _).mp (hZ ▸ hneighbor hx)).2.1
  apply CommutingNontrivial.source_normalized_edge_eq_bot h hvw _
    (le_inf ((map_subtype_le _).trans (sylowGenerated_le _))
      (hneighbor.trans (Z_le_stabilizer (family P) w)))
  · intro z hz
    obtain ⟨g, hg, hgz⟩ := graphLocalGroup_transitive h hB hS v ⟨w, hvw⟩ ⟨z, hz⟩
    exact ⟨g, hnv hg, hgz⟩
  · intro z hz
    obtain ⟨g, hg, hgz⟩ := graphLocalGroup_transitive h hB hS w ⟨v, hvw.symm⟩ ⟨z, hz⟩
    exact ⟨g, hnw hg, hgz⟩

/-- In characteristic two, killing central omega kills the whole local center. -/
theorem intrinsic_local_center_eq_bot_of_neighbor_central (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hZ : Z (family P) w = omegaCenterIn (graphLocalGroup (family P) w)) :
    center (graphLocalGroup (family P) v) = ⊥ := by
  let := finite_endpoints h
  let : Finite (graphLocalGroup (family P) v) := Finite.of_injective (inclusion (sylowGenerated_le _))
    (inclusion_injective _)
  have hn : stabilizer (family P) v ≤ normalizer (graphLocalGroup (family P) v : Set G) :=
    sylowGenerated_normalized _
  let : ((graphLocalGroup (family P) v).subgroupOf (stabilizer (family P) v)).Normal :=
    (normal_subgroupOf_iff_le_normalizer (sylowGenerated_le _)).mpr hn
  have hc : centralizer (pCore 2 (graphLocalGroup (family P) v) : Set (graphLocalGroup (family P) v)) ≤
      pCore 2 (graphLocalGroup (family P) v) :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe (sylowGenerated_le _))).mp
      (normal_core_selfCentralizing (DGS85.source_vertex_core_selfCentralizing h v)
        ((graphLocalGroup (family P) v).subgroupOf (stabilizer (family P) v)))
  have hp : IsPGroup 2 (center (graphLocalGroup (family P) v)) :=
    pCore_isPGroup.to_le ((center_le_centralizer _).trans hc)
  have hΩ := intrinsic_local_omega_eq_bot_of_neighbor_central h hB hS hvw hZ
  have hΩ' : (omega₁ (center (graphLocalGroup (family P) v)) (p := 2)).map
      (center (graphLocalGroup (family P) v)).subtype = ⊥ :=
    (map_eq_bot_iff_of_injective _ (graphLocalGroup (family P) v).subtype_injective).mp hΩ
  obtain ⟨n, hncard⟩ := hp.exists_card_eq
  by_cases hn0 : n = 0
  · exact card_eq_one.mp (by simpa [hn0] using hncard)
  · exact (omega₁_map_subtype_ne_bot (center (graphLocalGroup (family P) v)) 2
      (hncard ▸ dvd_pow_self 2 hn0) hΩ').elim

variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Source 9.1's opening control on the reduced graph, using the literal local
groups. No extra kernel-Sylow or local-obstruction premise is needed. -/
theorem reduced_critical_initial_clauses (h : HypothesisF11 L S)
    {a beta a' : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) a a')
    (hab : (graph (Reduction.reducedFamily L S)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S)).dist beta a' + 1 = b (Reduction.reducedFamily L S))
    (hb : 1 < b (Reduction.reducedFamily L S))
    (hcomm : ⁅Z (Reduction.reducedFamily L S) a, Z (Reduction.reducedFamily L S) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S) beta 1 ⊓ Q (Reduction.reducedFamily L S) a',
      V (Reduction.reducedFamily L S) a' 1⁆ = ⊥) :
    let F := Reduction.reducedFamily L S
    Odd (b F) ∧ 3 ≤ b F ∧ center (graphLocalGroup F a) = ⊥ ∧
      Z F beta = omegaCenterIn (graphLocalGroup F beta) ∧
      IsElementaryAbelian 2 (V F beta 1) ∧ IsElementaryAbelian 2 (V F a' 1) ∧
      ⁅⁅V F beta 1, V F a' 1⁆, V F beta 1⁆ = ⊥ ∧
      ⁅⁅V F beta 1, V F a' 1⁆, V F a' 1⁆ = ⊥ ∧
      ¬ V F beta 1 ≤ Q F a' ∧
      V F beta 1 ⊓ centralizer (V F a' 1 : Set (Reduction.G₀ L S)) =
        V F beta 1 ⊓ Q F a' := by
  obtain ⟨ho, hb3, hz, _⟩ := Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm
  obtain ⟨_, _, hev, hew, hqv, hqw, hesc⟩ := reduced_neighbor_quadratic h
    (Reduction.reduced_kernel_sylow h) hc hab.symm (by omega) hd
  exact ⟨ho, hb3, intrinsic_local_center_eq_bot_of_neighbor_central (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) hab hz,
    hz, hev, hew, hqv, hqw, hesc, reduced_neighbor_centralizer_eq_core_inter h beta a' hb hd htriv⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
