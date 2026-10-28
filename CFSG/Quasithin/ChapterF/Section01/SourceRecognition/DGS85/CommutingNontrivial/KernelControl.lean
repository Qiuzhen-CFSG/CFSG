module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.SourceApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LocalTransitivity
public import Theory.GroupAction.CubicTree.ThreeClosed

/-!
# Local-center vanishing and the neighboring-span action kernel

A normal subgroup escaping the full radius-one kernel covers the edge
cosets by rank-one Borel maximality. Applied to the centralizer of the
neighboring center span, this would make a nonzero neighboring center
normal under both local actions, contradicting faithfulness. Hence the
centralizer lies in the full local kernel.

An actual common Sylow puts the central omega of one local group in the
opposite center span. When that span is central in its local group, the
two transitive local normalizers force the omega subgroup to vanish.
Characteristic two then kills the entire local center. All normality is
relative to the displayed local groups; the ambient completion need not
be finite, and the graph need not be a tree.

Source: DGS, *Groups and Graphs* (1985), 3.2(c) and 8.1(b,c), pp.73,133.
`ReducedControl` applies these conclusions to the actual commuting
critical configuration and discharges reduced 6.2(d).
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Source 3.2(c) for the actual graph and two locally transitive normalizers. -/
theorem source_normalized_edge_eq_bot (h : LocallyRankOneTriple P B)
    {v w : Vertex (family P)} (_hvw : (graph (family P)).Adj v w)
    (K : Subgroup G) (hK : K ≤ stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hv : ∀ z, (graph (family P)).Adj v z →
      ∃ g ∈ normalizer (K : Set G), g • w = z)
    (hw : ∀ z, (graph (family P)).Adj w z →
      ∃ g ∈ normalizer (K : Set G), g • v = z) : K = ⊥ := by
  let := faithful_graph h
  exact Theory.GroupAction.CubicTree.normalized_edge_subgroup_eq_bot
    ⟨fun g _ _ ha => (Subgroup.CosetGeometry.translationGraphIso (family P) g).toHom.map_adj ha⟩
    (connected_graph h).preconnected K hK hv hw

/-- A normal subgroup escaping the full local kernel covers the edge cosets. -/
theorem source_normal_sup_edge (h : LocallyRankOneTriple P B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (N : Subgroup G) (hN : N ≤ stabilizer (family P) v)
    (hn : stabilizer (family P) v ≤ normalizer (N : Set G))
    (he : ¬ N ≤ U (family P) v) :
    N ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) w) = stabilizer (family P) v := by
  rcases source_edge_maximal h hvw _ le_sup_right (sup_le hN inf_le_left) with heq | heq
  · exfalso
    apply he
    have hNE : N ≤ stabilizer (family P) v ⊓ stabilizer (family P) w :=
      le_sup_left.trans heq.le
    let : (N.subgroupOf (stabilizer (family P) v)).Normal :=
      (normal_subgroupOf_iff_le_normalizer hN).mpr hn
    have hc : N.subgroupOf (stabilizer (family P) v) ≤
        ((stabilizer (family P) v ⊓ stabilizer (family P) w).subgroupOf
          (stabilizer (family P) v)).normalCore := normal_le_normalCore.mpr (comap_mono hNE)
    have hm := map_mono (f := (stabilizer (family P) v).subtype) hc
    rw [map_subgroupOf_eq_of_le hN] at hm
    exact hm.trans_eq (ballKernel_one_eq_map_normalCore (family P) hvw).symm
  · exact heq

/-- The local centralizer of the entire neighboring center span fixes every neighbor.
This proves 8.1(c) without assuming the commuting branch or the bound on b. -/
theorem source_span_centralizer_le_kernel (h : LocallyRankOneTriple P B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w) :
    stabilizer (family P) v ⊓ centralizer (V (family P) v 1 : Set G) ≤ U (family P) v := by
  let := finite_endpoints h
  let C := stabilizer (family P) v ⊓ centralizer (V (family P) v 1 : Set G)
  have hn : stabilizer (family P) v ≤ normalizer (C : Set G) :=
    (le_inf (stabilizer (family P) v).le_normalizer
      ((stabilizer_normalizes_V (family P) v 1).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  by_contra he
  have hcover := source_normal_sup_edge h hvw C inf_le_left hn he
  have hCv : C ≤ normalizer (Z (family P) w : Set G) :=
    (inf_le_right.trans (centralizer_le (Z_neighbor_le_V (family P) hvw))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hNv : stabilizer (family P) v ≤ normalizer (Z (family P) w : Set G) := by
    rw [← hcover]
    exact sup_le hCv (inf_le_right.trans (stabilizer_normalizes_Z (family P) w))
  have hbot : Z (family P) w = ⊥ := by
    apply source_normalized_edge_eq_bot h hvw _
      (le_inf (((source_Z_Q_U h w).1.trans (map_subtype_le _)).trans
        ((source_Z_Q_U h w).2.trans
          ((ballKernel_one_le_edge (family P) hvw.symm).trans inf_le_right)))
        (Z_le_stabilizer (family P) w))
    · intro z hz
      obtain ⟨g, hg, hgz⟩ := locally_transitive (family P) hvw hz
      exact ⟨g, hNv hg, hgz⟩
    · intro z hz
      obtain ⟨g, hg, hgz⟩ := locally_transitive (family P) hvw.symm hz
      exact ⟨g, stabilizer_normalizes_Z (family P) w hg, hgz⟩
  obtain ⟨g, hg⟩ := Subgroup.CosetGeometry.exists_smul_base (family P) w
  rw [← hg, Z_translate, map_eq_bot_iff_of_injective _ (MulAut.conj g).injective] at hbot
  exact base_Z_ne_bot h _ hbot

/-- Characteristic two transports to the literal stabilizer, not just its base representative. -/
theorem source_vertex_core_selfCentralizing (h : LocallyRankOneTriple P B)
    (v : Vertex (family P)) :
    centralizer (pCore 2 (stabilizer (family P) v) : Set (stabilizer (family P) v)) ≤
      pCore 2 (stabilizer (family P) v) := by
  obtain ⟨g, hg⟩ := Subgroup.CosetGeometry.exists_smul_base (family P) v
  rw [← hg, stabilizer_translate]
  apply (Theory.Quasithin.centralizer_pCore_le_iff 2
    ((stabilizer (family P) (base (family P) v.type)).equivMapOfInjective
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)).mp
  change centralizer (pCore 2 (MulAction.stabilizer G
    (Subgroup.CosetGeometry.base (family P) v.type)) :
      Set (MulAction.stabilizer G (Subgroup.CosetGeometry.base (family P) v.type))) ≤
      pCore 2 (MulAction.stabilizer G (Subgroup.CosetGeometry.base (family P) v.type))
  rw [Subgroup.CosetGeometry.stabilizer_base]
  cases v.type
  · exact source_core_selfCentralizing (Classical.choice (h.local_data 0))
  · exact source_core_selfCentralizing (Classical.choice (h.local_data 1))

/-- Central omega of a local group is contained in the center span across an edge
when that local group contains an actual common Sylow. -/
theorem local_omega_le_neighbor_Z (_h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w) :
    omegaCenterIn (d.localGroup v) ≤ Z (family P) w := by
  obtain ⟨T, T', hTT⟩ := d.common_sylow v w hvw
  have hcentral : omegaCenterIn (d.localGroup v) ≤ centralizer (d.localGroup v : Set G) :=
    fun x hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1
  have hT : omegaCenterIn (d.localGroup v) ≤
      (T : Subgroup (stabilizer (family P) v)).map (stabilizer (family P) v).subtype :=
    le_sylow_image_of_normalizes _ T rfl (IsElementaryAbelian.isPGroup 2 _)
      ((map_subtype_le _).trans (d.local_le v))
      ((hcentral.trans (centralizer_le (d.sylow_le v T))).trans
        (Subgroup.centralizer_le_normalizer _))
  have hΩ : omegaCenterIn (d.localGroup v) ≤ omegaCenterIn
      ((T : Subgroup (stabilizer (family P) v)).map (stabilizer (family P) v).subtype) := by
    intro x hx
    exact (mem_omegaCenterIn_iff _ _).mpr ⟨hT hx,
      centralizer_le (d.sylow_le v T) (hcentral hx),
      ((mem_omegaCenterIn_iff _ _).mp hx).2.2⟩
  rw [hTT] at hΩ
  exact hΩ.trans (le_iSup (fun R : Sylow 2 (stabilizer (family P) w) =>
    omegaCenterIn ((R : Subgroup (stabilizer (family P) w)).map
      (stabilizer (family P) w).subtype)) T')

/-- Source 8.1(b)'s central omega vanishes by the genuine local-normalizer obstruction. -/
theorem local_omega_eq_bot_of_neighbor_central (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hZ : Z (family P) w = omegaCenterIn (d.localGroup w)) :
    omegaCenterIn (d.localGroup v) = ⊥ := by
  have hneighbor := local_omega_le_neighbor_Z h d hvw
  have hnv : d.localGroup v ≤ normalizer (omegaCenterIn (d.localGroup v) : Set G) :=
    (d.localGroup v).le_normalizer.trans (normalizer_le_normalizer_omegaCenterIn _)
  have hnw : d.localGroup w ≤ normalizer (omegaCenterIn (d.localGroup v) : Set G) := by
    apply (le_centralizer_iff.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
    intro x hx
    exact ((mem_omegaCenterIn_iff _ _).mp (hZ ▸ hneighbor hx)).2.1
  apply source_normalized_edge_eq_bot h hvw _
    (le_inf ((map_subtype_le _).trans (d.local_le v))
      (hneighbor.trans (Z_le_stabilizer (family P) w)))
  · intro z hz
    obtain ⟨g, hg, hgz⟩ := d.transitive v ⟨w, hvw⟩ ⟨z, hz⟩
    exact ⟨g, hnv hg, hgz⟩
  · intro z hz
    obtain ⟨g, hg, hgz⟩ := d.transitive w ⟨v, hvw.symm⟩ ⟨z, hz⟩
    exact ⟨g, hnw hg, hgz⟩

/-- In characteristic two, killing central omega kills the whole local center. -/
theorem local_center_eq_bot_of_neighbor_central (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hZ : Z (family P) w = omegaCenterIn (d.localGroup w)) :
    center (d.localGroup v) = ⊥ := by
  let := finite_endpoints h
  let : Finite (d.localGroup v) := Finite.of_injective (inclusion (d.local_le v))
    (inclusion_injective _)
  have hn : stabilizer (family P) v ≤ normalizer (d.localGroup v : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    change (d.localGroup v).map (MulAut.conj g).toMonoidHom = _
    rw [← d.conjugate]
    exact congrArg d.localGroup hg
  let : ((d.localGroup v).subgroupOf (stabilizer (family P) v)).Normal :=
    (normal_subgroupOf_iff_le_normalizer (d.local_le v)).mpr hn
  have hc : centralizer (pCore 2 (d.localGroup v) : Set (d.localGroup v)) ≤
      pCore 2 (d.localGroup v) :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe (d.local_le v))).mp
      (normal_core_selfCentralizing (source_vertex_core_selfCentralizing h v)
        ((d.localGroup v).subgroupOf (stabilizer (family P) v)))
  have hp : IsPGroup 2 (center (d.localGroup v)) :=
    pCore_isPGroup.to_le ((center_le_centralizer _).trans hc)
  have hΩ := local_omega_eq_bot_of_neighbor_central h d hvw hZ
  have hΩ' : (omega₁ (center (d.localGroup v)) (p := 2)).map
      (center (d.localGroup v)).subtype = ⊥ :=
    (map_eq_bot_iff_of_injective _ (d.localGroup v).subtype_injective).mp hΩ
  obtain ⟨n, hncard⟩ := hp.exists_card_eq
  by_cases hn0 : n = 0
  · exact card_eq_one.mp (by simpa [hn0] using hncard)
  · exact (omega₁_map_subtype_ne_bot (center (d.localGroup v)) 2
      (hncard ▸ dvd_pow_self 2 hn0) hΩ').elim

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
