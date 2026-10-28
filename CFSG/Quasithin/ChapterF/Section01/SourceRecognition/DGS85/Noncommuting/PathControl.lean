module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.GraphRadius
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LocalTransitivity
public import Theory.GroupTheory.Amalgam.LocalCover

/-!
# Critical-path control and faithful local actors

The source edge is maximal in its full vertex stabilizer. Short balls act at
vertices within their distance budget, and noncommuting centers at distance
at most b form a new critical pair. The vertex core lies in every incident
edge core. Finally, actors covering the full edge cosets inherit the faithful
common-normal obstruction by a word factorization in the original completion.
These are the path and normality steps consumed in the proof of (7.3).

Source: DGS, *Groups and Graphs* (1985), (3.2)(c), (6.0), (7.3), pp.72,118,127.
-/

public section
open Subgroup
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Local maximality at the literal edge, in the relative subgroup lattice. -/
theorem graph_edge_isCoatom (h : LocallyRankOneTriple P B)
    {v w : Vertex (family P)} (hadj : (graph (family P)).Adj v w) :
    IsCoatom ((stabilizer (family P) w).subgroupOf (stabilizer (family P) v)) := by
  let H := stabilizer (family P) v
  let K := stabilizer (family P) w
  have hproper : H ⊓ K ≠ H := by
    obtain ⟨g,hP,hE⟩ := source_edge_transport h hadj
    intro he
    have hB : B = family P v.type := by
      apply map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
      exact hE.symm.trans (he.trans hP)
    have hlt : B < family P v.type := by
      cases ht : v.type
      · exact source_borel_lt (Classical.choice (h.local_data 0))
      · exact source_borel_lt (Classical.choice (h.local_data 1))
    exact hlt.ne hB
  refine ⟨?_,?_⟩
  · intro he
    apply hproper
    change K.subgroupOf H = ⊤ at he
    have hm := congrArg (Subgroup.map H.subtype) he
    simpa only [subgroupOf_map_subtype, ← MonoidHom.range_eq_map, range_subtype,
      inf_comm] using hm
  · intro M hM
    have hEM : H ⊓ K ≤ M.map H.subtype := by
      have hm := map_mono (f := H.subtype) hM.le
      rwa [subgroupOf_map_subtype, inf_comm] at hm
    rcases source_edge_maximal h hadj (M.map H.subtype) hEM (map_subtype_le _) with he | he
    · have hm : M = K.subgroupOf H := by
        apply map_injective H.subtype_injective
        simpa only [subgroupOf_map_subtype, inf_comm] using he
      exact (hM.ne hm.symm).elim
    · apply map_injective H.subtype_injective
      simpa only [← MonoidHom.range_eq_map,range_subtype] using he

/-- A radius subgroup acts at every vertex within the critical-distance budget. -/
theorem graph_V_le_stabilizer_of_distance (h : LocallyRankOneTriple P B)
    {v w : Vertex (family P)} {i : ℕ}
    (hd : (graph (family P)).dist v w + i ≤ b (family P)) :
    V (family P) v i ≤ stabilizer (family P) w := by
  let := finite_endpoints h
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  apply Z_le_stabilizer_of_dist_le_b (family P) h.generate
  have hx' := (mem_ball_iff (family P) h.generate v x i).mp hx
  have ht := (connected_graph h).dist_triangle (u := x) (v := v) (w := w)
  rw [SimpleGraph.dist_comm (u := x) (v := v)] at ht
  omega

/-- Noncommutation at distance at most b constructs a new ordered critical pair. -/
theorem graph_critical_of_noncommuting (h : LocallyRankOneTriple P B)
    (hS : ∀ v, Stellmacher.IsSylowSubgroupIn (Q (family P) v) (U (family P) v))
    {v w : Vertex (family P)} (hd : (graph (family P)).dist v w ≤ b (family P))
    (hne : ⁅Z (family P) v, Z (family P) w⁆ ≠ ⊥) :
    IsCriticalPair (family P) v w := by
  have hdist : (graph (family P)).dist v w = b (family P) := by
    apply le_antisymm hd
    by_contra hn
    exact hne (commutator_eq_bot_iff_le_centralizer.mpr
      (graph_centers_commute_of_short h hS (by omega)))
  let := graph_Z_elementary h v
  refine ⟨hdist,?_⟩
  apply critical_center_escapes_local_kernel (stabilizer (family P) w)
    (U (family P) w) (Z (family P) w) (Z (family P) v)
    (U_le_stabilizer _ _) (IsElementaryAbelian.isPGroup 2 _) (hS w)
    (graph_Q_centralizes_Z h w)
  rwa [commutator_comm]

/-- The vertex core lies in the actual two-core of every incident edge. -/
theorem graph_Q_le_edgeCore (h : LocallyRankOneTriple P B)
    {v w : Vertex (family P)} (hadj : (graph (family P)).Adj v w) :
    Q (family P) v ≤ (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 := by
  have hQE : Q (family P) v ≤ stabilizer (family P) v ⊓ stabilizer (family P) w :=
    (source_Z_Q_U h v).2.trans (ballKernel_one_le_edge (family P) hadj)
  apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _) hQE
  exact inf_le_left.trans ((stabilizer (family P) v).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))

/-- Edge transitivity and the original full Borel give a faithful edge core. -/
theorem graph_edge_normalCore_eq_bot (h : LocallyRankOneTriple P B)
    {v w : Vertex (family P)} (hadj : (graph (family P)).Adj v w) :
    (stabilizer (family P) v ⊓ stabilizer (family P) w).normalCore = ⊥ := by
  let K := (stabilizer (family P) v ⊓ stabilizer (family P) w).normalCore
  obtain ⟨g,_,hE⟩ := source_edge_transport h hadj
  have hKB : K ≤ B := by
    have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
      (show K ≤ stabilizer (family P) v ⊓ stabilizer (family P) w from normalCore_le _)
    change K.map (MulAut.conj g⁻¹) ≤
      (stabilizer (family P) v ⊓ stabilizer (family P) w).map
        (MulAut.conj g⁻¹).toMonoidHom at hm
    rw [Subgroup.Normal.map_conj_eq] at hm
    rw [hE,map_map] at hm
    have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id G := by ext x; simp [mul_assoc]
    simpa only [he,map_id] using hm
  exact h.faithful K inferInstance hKB

/-- The two full vertex groups at any edge generate the original completion. -/
theorem graph_adjacent_generate (h : LocallyRankOneTriple P B)
    {v w : Vertex (family P)} (hadj : (graph (family P)).Adj v w) :
    stabilizer (family P) v ⊔ stabilizer (family P) w = ⊤ := by
  obtain ⟨g,hv,hw⟩ := incident_common_translate (family P) hadj.2
  have hb : stabilizer (family P) (base (family P) v.type) ⊔
      stabilizer (family P) (base (family P) w.type) = ⊤ := by
    simp only [stabilizer, Subgroup.CosetGeometry.stabilizer_base]
    have ht := hadj.1
    cases hi : v.type <;> cases hj : w.type
    · exact (ht (hi.trans hj.symm)).elim
    · exact h.generate
    · exact sup_comm _ _ |>.trans h.generate
    · exact (ht (hi.trans hj.symm)).elim
  rw [← hv,← hw,stabilizer_translate,stabilizer_translate,← Subgroup.map_sup,hb]
  exact map_top_of_surjective _ (MulAut.conj g).surjective

/-- The common-normal obstruction also holds for local actors covering the
full edge cosets. The actors need not be the full vertex stabilizers. -/
theorem graph_local_common_normal_eq_bot (h : LocallyRankOneTriple P B)
    {v w : Vertex (family P)} (hadj : (graph (family P)).Adj v w)
    (L M K : Subgroup G)
    (hL : ∀ a ∈ stabilizer (family P) v, ∃ l ∈ L,
      ∃ t ∈ stabilizer (family P) v ⊓ stabilizer (family P) w, a = l*t)
    (hM : ∀ a ∈ stabilizer (family P) w, ∃ m ∈ M,
      ∃ t ∈ stabilizer (family P) v ⊓ stabilizer (family P) w, a = m*t)
    (hK : K ≤ stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hnL : L ≤ normalizer (K : Set G)) (hnM : M ≤ normalizer (K : Set G)) : K = ⊥ := by
  apply local_pair_normalized_eq_bot (stabilizer (family P) v)
    (stabilizer (family P) w) K (L ⊔ M)
    (graph_adjacent_generate h hadj) (graph_edge_normalCore_eq_bot h hadj)
    hK (sup_le hnL hnM)
  · intro a ha
    obtain ⟨l,hl,t,ht,he⟩ := hL a ha
    exact ⟨l,(show L ≤ L ⊔ M from le_sup_left) hl,t,ht,he⟩
  · intro a ha
    obtain ⟨m,hm,t,ht,he⟩ := hM a ha
    exact ⟨m,(show M ≤ L ⊔ M from le_sup_right) hm,t,ht,he⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
