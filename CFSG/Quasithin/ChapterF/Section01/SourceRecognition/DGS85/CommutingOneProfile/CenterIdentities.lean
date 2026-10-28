module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.EarlierInputs
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.KernelControl
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.NeighborIntersection

/-!
# Intrinsic local centers in the commuting distance-one case

For a commuting critical pair at distance one, the intrinsic local group at
beta has omega-center Zβ and the alpha local group has trivial center, as
in DGS (11.1)(a,b). Common edge Sylows place each local omega-center in every
neighboring Z-layer. Local transitivity and faithfulness then kill the
opposite omega-center; characteristic two kills its whole center.

In particular Zβ lies in every neighboring center and hence in the
neighboring-core intersection used in (11.6). The application uses the
literal reduced F1.11 graph. No still-open earlier-local obstruction is
needed for these identities, and the full local kernel remains distinct
from the two-core.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.1)(a,b), printed p.167, and the setup of (11.6), printed p.172.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem local_omega_le_neighbor (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w) :
    omegaCenterIn (graphLocalGroup (family P) v) ≤ Z (family P) w := by
  let := finite_endpoints h
  obtain ⟨T, T', hTT⟩ := source_common_edge_sylow h hB hS hvw
  have hcentral : omegaCenterIn (graphLocalGroup (family P) v) ≤
      centralizer (graphLocalGroup (family P) v : Set G) :=
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

private theorem local_omega_eq_bot (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hZ : Z (family P) w = omegaCenterIn (graphLocalGroup (family P) w)) :
    omegaCenterIn (graphLocalGroup (family P) v) = ⊥ := by
  let := finite_endpoints h
  have hneighbor := local_omega_le_neighbor h hB hS hvw
  have hnv : graphLocalGroup (family P) v ≤
      normalizer (omegaCenterIn (graphLocalGroup (family P) v) : Set G) :=
    (graphLocalGroup (family P) v).le_normalizer.trans
      (normalizer_le_normalizer_omegaCenterIn _)
  have hnw : graphLocalGroup (family P) w ≤
      normalizer (omegaCenterIn (graphLocalGroup (family P) v) : Set G) := by
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

private theorem local_center_eq_bot (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hZ : Z (family P) w = omegaCenterIn (graphLocalGroup (family P) w)) :
    center (graphLocalGroup (family P) v) = ⊥ := by
  let := finite_endpoints h
  let L := graphLocalGroup (family P) v
  have hL : L ≤ stabilizer (family P) v := sylowGenerated_le _
  let : Finite L := Finite.of_injective (inclusion hL) (inclusion_injective _)
  let : (L.subgroupOf (stabilizer (family P) v)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hL).mpr (sylowGenerated_normalized _)
  have hc : centralizer (pCore 2 L : Set L) ≤ pCore 2 L :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hL)).mp
      (normal_core_selfCentralizing
        (CommutingNontrivial.source_vertex_core_selfCentralizing h v)
        (L.subgroupOf (stabilizer (family P) v)))
  have hp : IsPGroup 2 (center L) :=
    pCore_isPGroup.to_le ((center_le_centralizer _).trans hc)
  have hΩ := local_omega_eq_bot h hB hS hvw hZ
  have hΩ' : (omega₁ (center L) (p := 2)).map (center L).subtype = ⊥ :=
    (map_eq_bot_iff_of_injective _ L.subtype_injective).mp hΩ
  obtain ⟨n, hncard⟩ := hp.exists_card_eq
  by_cases hn0 : n = 0
  · exact card_eq_one.mp (by simpa [hn0] using hncard)
  · exact (omega₁_map_subtype_ne_bot (center L) 2
      (hncard ▸ dvd_pow_self 2 hn0) hΩ').elim

/-- The two center identities of DGS (11.1), for the intrinsic source local groups. -/
theorem source_commuting_one_center_identities (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a beta : Vertex (family P)} (hc : IsCriticalPair (family P) a beta)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a, Z (family P) beta⁆ = ⊥) :
    Z (family P) beta = omegaCenterIn (graphLocalGroup (family P) beta) ∧
      center (graphLocalGroup (family P) a) = ⊥ := by
  let := finite_endpoints h
  have he := CommutingNontrivial.critical_end_center_of_commuting (family P)
    h.generate (fun v => (source_Z_Q_U h v).1) (fun v => (source_Z_Q_U h v).2)
    hc hcomm (graphLocalGroup (family P) beta) (graphLocalGroup_sylow_or_center h hB hS beta)
  exact ⟨he, local_center_eq_bot h hB hS (source_critical_one_adjacent hc hb) he⟩

/-- The beta center lies in every neighboring center, with the intrinsic
local group and actual common edge Sylows retained. -/
theorem source_commuting_one_center_le_neighbor (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a beta c : Vertex (family P)} (hc : IsCriticalPair (family P) a beta)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a, Z (family P) beta⁆ = ⊥)
    (hbc : (graph (family P)).Adj beta c) :
    Z (family P) beta ≤ Z (family P) c := by
  rw [(source_commuting_one_center_identities h hB hS hc hb hcomm).1]
  exact local_omega_le_neighbor h hB hS hbc

/-- The lower inclusion in source (11.6)(a), for the actual neighboring cores. -/
theorem source_commuting_one_center_le_neighbor_intersection (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a beta : Vertex (family P)} (hc : IsCriticalPair (family P) a beta)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a, Z (family P) beta⁆ = ⊥) :
    Z (family P) beta ≤ neighborCoreIntersection (family P) beta := by
  apply le_iInf
  intro c
  exact (source_commuting_one_center_le_neighbor h hB hS hc hb hcomm c.property).trans
    ((source_Z_Q_U h c.val).1.trans (map_subtype_le _))

variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Application of (11.1)(a,b) to the literal reduced F1.11 graph. -/
theorem reduced_commuting_one_center_identities (h : HypothesisF11 L S)
    {a beta : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) a beta)
    (hb : DGS85.b (Reduction.reducedFamily L S) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily L S) a, Z (Reduction.reducedFamily L S) beta⁆ = ⊥) :
    Z (Reduction.reducedFamily L S) beta =
        omegaCenterIn (graphLocalGroup (Reduction.reducedFamily L S) beta) ∧
      center (graphLocalGroup (Reduction.reducedFamily L S) a) = ⊥ :=
  source_commuting_one_center_identities (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) hc hb hcomm

/-- The lower neighboring-core inclusion on the original reduced graph. -/
theorem reduced_commuting_one_center_le_neighbor_intersection (h : HypothesisF11 L S)
    {a beta : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) a beta)
    (hb : DGS85.b (Reduction.reducedFamily L S) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily L S) a, Z (Reduction.reducedFamily L S) beta⁆ = ⊥) :
    Z (Reduction.reducedFamily L S) beta ≤
      neighborCoreIntersection (Reduction.reducedFamily L S) beta :=
  source_commuting_one_center_le_neighbor_intersection (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) hc hb hcomm

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
