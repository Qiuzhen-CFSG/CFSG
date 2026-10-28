module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SourceTriple
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.SourceSections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.RadiusEscape
public import Theory.ElementaryAbelian.CommutingFamily

/-!
# Short-radius control at the noncommuting critical pair

Minimality puts a short-distance center inside U, the full local permutation
kernel. Its two-group property and the earlier (6.2)(d) Sylow statement then
put it inside Q, the two-core. This gives the radius groups' core containment,
two-group property, and centralization of the critical commutator. Pairwise
short distances also give elementary abelianness when twice the radius is
less than b. Translation proves the needed relative normalizer statements.

The escape theorems prove the actual radius-one and radius-two escape
mechanisms of (7.2), assuming the (7.1) Sylow product and local generation.
Radius one retains the earlier (6.6) normality obstruction. For radius two,
the common-normal contradiction is proved from the original triple's
faithfulness, connectedness and exact adjacent stabilizers. No tree or
finite ambient completion is assumed. These results do not bound b.

Source: DGS, *Groups and Graphs* (1985), (7.1)--(7.5), printed pp.126--129.
The kernel-Sylow premise is owned by the Chapter 6 setup producer; selection
of a generating neighbor is derived from reverse escape and the maximality
of local point stabilizers. Recognition and the later Chapter 7 distance
steps remain with the noncommuting owner.
-/

public section
open Subgroup
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The source center span is elementary abelian inside the actual core omega. -/
theorem graph_Z_elementary (h : LocallyRankOneTriple P B) (v : Vertex (family P)) :
    IsElementaryAbelian 2 (Z (family P) v) :=
  IsElementaryAbelian.of_le (source_Z_Q_U h v).1

/-- The original vertex two-core centralizes its center span. -/
theorem graph_Q_centralizes_Z (h : LocallyRankOneTriple P B) (v : Vertex (family P)) :
    Q (family P) v ≤ centralizer (Z (family P) v : Set G) := by
  apply le_centralizer_iff.mpr
  intro z hz
  exact ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h v).1 hz)).2.1

private theorem graph_Q_normalized (v : Vertex (family P)) :
    stabilizer (family P) v ≤ normalizer (Q (family P) v : Set G) := by
  simpa only [Q, pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
    using (pCore 2 (stabilizer (family P) v)).le_normalizer_map
      (stabilizer (family P) v).subtype

/-- The Sylow premise upgrades short-distance containment in U to containment in Q. -/
theorem graph_Z_le_Q_of_short (h : LocallyRankOneTriple P B)
    (hS : ∀ v, Stellmacher.IsSylowSubgroupIn (Q (family P) v) (U (family P) v))
    {v w : Vertex (family P)} (hd : (graph (family P)).dist v w < b (family P)) :
    Z (family P) v ≤ Q (family P) w := by
  let := graph_Z_elementary h v
  have hu := Z_le_U_of_dist_lt_b (family P) v w hd
  have he := inf_eq_inf_of_normal_sylow (Z (family P) v) (U (family P) w)
    (Q (family P) w) (IsElementaryAbelian.isPGroup 2 _)
    (source_Z_Q_U h w).2 ((U_le_stabilizer _ _).trans (graph_Q_normalized w)) (hS w)
  rw [inf_of_le_left hu] at he
  exact he.le.trans inf_le_right

/-- Every generator of a short-radius subgroup lies in the same original core. -/
theorem graph_V_le_Q_of_short (h : LocallyRankOneTriple P B)
    (hS : ∀ v, Stellmacher.IsSylowSubgroupIn (Q (family P) v) (U (family P) v))
    (v : Vertex (family P)) {i : ℕ} (hi : i < b (family P)) :
    V (family P) v i ≤ Q (family P) v := by
  apply iSup_le
  intro w
  apply iSup_le
  intro hw
  apply graph_Z_le_Q_of_short h hS (v := w) (w := v)
  rw [SimpleGraph.dist_comm]
  exact ((mem_ball_iff (family P) h.generate v w i).mp hw).trans_lt hi

/-- Short-radius groups are two-groups even when they need not yet be abelian. -/
theorem graph_V_isPGroup_of_short (h : LocallyRankOneTriple P B)
    (hS : ∀ v, Stellmacher.IsSylowSubgroupIn (Q (family P) v) (U (family P) v))
    (v : Vertex (family P)) {i : ℕ} (hi : i < b (family P)) :
    IsPGroup 2 (V (family P) v i) :=
  (isPGroup_pCoreIn 2 (stabilizer (family P) v)).to_le
    (graph_V_le_Q_of_short h hS v hi)

/-- The original stabilizer normalizes every radius subgroup by translation. -/
theorem graph_stabilizer_normalizes_V (h : LocallyRankOneTriple P B)
    (v : Vertex (family P)) (i : ℕ) :
    stabilizer (family P) v ≤ normalizer (V (family P) v i : Set G) := by
  let := finite_endpoints h
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (V (family P) v i).map (MulAut.conj g).toMonoidHom = _
  rw [← V_translate (family P) g v i, hg]

/-- An adjacent radius subgroup lies in the next radius about the first vertex. -/
theorem graph_V_adjacent_le
    {v w : Vertex (family P)} (hadj : (graph (family P)).Adj v w) (i : ℕ) :
    V (family P) w i ≤ V (family P) v (i + 1) := by
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  exact le_iSup_of_le x (le_iSup_of_le (ball_subset_succ _ hadj i hx) le_rfl)

/-- Centers at distance below b commute through the actual two-core. -/
theorem graph_centers_commute_of_short (h : LocallyRankOneTriple P B)
    (hS : ∀ v, Stellmacher.IsSylowSubgroupIn (Q (family P) v) (U (family P) v))
    {v w : Vertex (family P)} (hd : (graph (family P)).dist v w < b (family P)) :
    Z (family P) v ≤ centralizer (Z (family P) w : Set G) :=
  (graph_Z_le_Q_of_short h hS (v := v) (w := w) hd).trans (graph_Q_centralizes_Z h w)

/-- The radius group centralizes the critical commutator whenever its radius is below b. -/
theorem graph_V_centralizes_commutator (h : LocallyRankOneTriple P B)
    (hS : ∀ v, Stellmacher.IsSylowSubgroupIn (Q (family P) v) (U (family P) v))
    {v w : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    {i : ℕ} (hi : i < b (family P)) :
    ⁅V (family P) v i, ⁅Z (family P) v, Z (family P) w⁆⁆ = ⊥ := by
  let := finite_endpoints h
  apply commutator_eq_bot_iff_le_centralizer.mpr
  exact ((graph_V_le_Q_of_short h hS v hi).trans (graph_Q_centralizes_Z h v)).trans
    (centralizer_le ((criticalPair_centers (family P) h.generate (v := v) (w := w) hc).2.trans inf_le_left))

/-- Centers throughout a small ball commute, so their join is elementary abelian. -/
theorem graph_V_elementary_of_twice_radius_lt (h : LocallyRankOneTriple P B)
    (hS : ∀ v, Stellmacher.IsSylowSubgroupIn (Q (family P) v) (U (family P) v))
    (v : Vertex (family P)) {i : ℕ} (hi : 2 * i < b (family P)) :
    IsElementaryAbelian 2 (V (family P) v i) := by
  let E (w : ball (family P) v i) := Z (family P) w.val
  let : ∀ w, IsElementaryAbelian 2 (E w) := fun w => graph_Z_elementary h w.val
  have he : V (family P) v i = ⨆ w, E w := by
    simp only [V, E, iSup_subtype]
  rw [he]
  apply IsElementaryAbelian.iSup_of_le_centralizer
  intro x y
  apply graph_centers_commute_of_short h hS (v := x.val) (w := y.val)
  have hx := (mem_ball_iff (family P) h.generate v x.val i).mp x.property
  have hy := (mem_ball_iff (family P) h.generate v y.val i).mp y.property
  have ht := (connected_graph h).dist_triangle (u := x.val) (v := v) (w := y.val)
  rw [SimpleGraph.dist_comm (u := x.val) (v := v)] at ht
  omega

/-- Noncommutation makes the reversed ordered pair critical for the same two-orbit minimum. -/
theorem graph_criticalPair_reverse (h : LocallyRankOneTriple P B)
    (hS : ∀ v, Stellmacher.IsSylowSubgroupIn (Q (family P) v) (U (family P) v))
    {v w : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v, Z (family P) w⁆ ≠ ⊥) :
    IsCriticalPair (family P) w v := by
  let := graph_Z_elementary h w
  refine ⟨(SimpleGraph.dist_comm (u := w) (v := v)).trans hc.1, ?_⟩
  exact critical_center_escapes_local_kernel (stabilizer (family P) v)
    (U (family P) v) (Z (family P) v) (Z (family P) w)
    (U_le_stabilizer _ _) (IsElementaryAbelian.isPGroup 2 _) (hS v)
    (graph_Q_centralizes_Z h v) hne

private theorem graph_edge_generation (h : LocallyRankOneTriple P B)
    {v w : Vertex (family P)} (hadj : (graph (family P)).Adj v w) :
    stabilizer (family P) v ⊔ stabilizer (family P) w = ⊤ := by
  obtain ⟨g, hv, hw⟩ := incident_common_translate (family P) hadj.2
  have hb : stabilizer (family P) (base (family P) v.type) ⊔
      stabilizer (family P) (base (family P) w.type) = ⊤ := by
    simp only [stabilizer, Subgroup.CosetGeometry.stabilizer_base]
    have ht := hadj.1
    cases hi : v.type <;> cases hj : w.type
    · exact (ht (hi.trans hj.symm)).elim
    · exact h.generate
    · exact sup_comm _ _ |>.trans h.generate
    · exact (ht (hi.trans hj.symm)).elim
  rw [← hv, ← hw, stabilizer_translate, stabilizer_translate, ← Subgroup.map_sup, hb]
  exact map_top_of_surjective _ (MulAut.conj g).surjective

private theorem graph_common_normal_eq_bot (h : LocallyRankOneTriple P B)
    {v w : Vertex (family P)} (hadj : (graph (family P)).Adj v w)
    (K : Subgroup G) (hK : K ≤ stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hvK : stabilizer (family P) v ≤ normalizer (K : Set G))
    (hwK : stabilizer (family P) w ≤ normalizer (K : Set G)) : K = ⊥ := by
  have hn : normalizer (K : Set G) = ⊤ := by
    apply top_unique
    rw [← graph_edge_generation h hadj]
    exact sup_le hvK hwK
  let : K.Normal := normalizer_eq_top_iff.mp hn
  obtain ⟨g, hv, hw⟩ := incident_common_translate (family P) hadj.2
  have hbase (x : Vertex (family P)) (hx : g • base (family P) x.type = x)
      (hKx : K ≤ stabilizer (family P) x) : K ≤ family P x.type := by
    have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hKx
    change K.map (MulAut.conj g⁻¹) ≤
      (stabilizer (family P) x).map (MulAut.conj g⁻¹).toMonoidHom at hm
    rw [Subgroup.Normal.map_conj_eq] at hm
    rw [← stabilizer_translate, ← hx, inv_smul_smul] at hm
    exact hm.trans_eq (Subgroup.CosetGeometry.stabilizer_base (family P) x.type)
  have hv' := hbase v hv (hK.trans inf_le_left)
  have hw' := hbase w hw (hK.trans inf_le_right)
  apply h.faithful K inferInstance
  rw [← h.intersection]
  have ht := hadj.1
  cases hi : v.type <;> cases hj : w.type
  · exact (ht (hi.trans hj.symm)).elim
  · exact le_inf (by simpa only [hi, family] using hv') (by simpa only [hj, family] using hw')
  · exact le_inf (by simpa only [hj, family] using hw') (by simpa only [hi, family] using hv')
  · exact (ht (hi.trans hj.symm)).elim

private theorem graph_Z_normalized (h : LocallyRankOneTriple P B)
    (v : Vertex (family P)) :
    stabilizer (family P) v ≤ normalizer (Z (family P) v : Set G) := by
  let := finite_endpoints h
  exact (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ _)).mp (Z_normal _ _)

/-- The actual radius-one escape, with the earlier center-product obstruction explicit. -/
theorem graph_radius_one_escape (h : LocallyRankOneTriple P B)
    (hS : ∀ v, Stellmacher.IsSylowSubgroupIn (Q (family P) v) (U (family P) v))
    {v w u : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hb : 2 < b (family P)) (hu : (graph (family P)).Adj v u)
    (hSyl : Stellmacher.IsSylowSubgroupIn
      (Z (family P) v ⊔ Q (family P) w) (stabilizer (family P) w))
    (hgen : Z (family P) w ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) u) =
      stabilizer (family P) v)
    (hobs : ¬ stabilizer (family P) v ≤
      normalizer ((Z (family P) u ⊔ Z (family P) v : Subgroup G) : Set G)) :
    ¬ V (family P) v 1 ≤ stabilizer (family P) w := by
  let := finite_endpoints h
  have h1 : 1 < b (family P) := by omega
  have hwv := (criticalPair_centers (family P) h.generate hc).1
  have hvw := Z_le_stabilizer_of_dist_le_b (family P) h.generate v w hc.1.le
  apply source_radius_escape_of_product_obstruction
    (stabilizer (family P) w) (stabilizer (family P) v) (stabilizer (family P) u)
    (Z (family P) v) (Z (family P) w) (Z (family P) u) (V (family P) v 1)
    (graph_V_isPGroup_of_short h hS v h1)
    (((graph_V_le_Q_of_short h hS v h1).trans (Q_le_stabilizer _ _)).trans
      (graph_Z_normalized h v)) (Z_le_V _ _ _)
    (hvw.trans (graph_Z_normalized h w)) (hwv.trans (graph_Z_normalized h v))
    (graph_Q_centralizes_Z h w) hSyl
    (le_iSup_of_le u (le_iSup_of_le ((mem_ball_one _ _ _).mpr (Or.inl hu)) le_rfl))
    hgen (graph_Z_normalized h v) (graph_Z_normalized h u) hobs

/-- The actual radius-two escape. Faithfulness discharges the common-normal obstruction. -/
theorem graph_radius_two_escape (h : LocallyRankOneTriple P B)
    (hS : ∀ v, Stellmacher.IsSylowSubgroupIn (Q (family P) v) (U (family P) v))
    {v w u : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v, Z (family P) w⁆ ≠ ⊥)
    (hb : 2 < b (family P)) (hu : (graph (family P)).Adj v u)
    (hSyl : Stellmacher.IsSylowSubgroupIn
      (Z (family P) v ⊔ Q (family P) w) (stabilizer (family P) w))
    (hgen : Z (family P) w ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) u) =
      stabilizer (family P) v) :
    ¬ V (family P) v 2 ≤ stabilizer (family P) w := by
  let := finite_endpoints h
  have h1 : 1 < b (family P) := by omega
  have hwv := (criticalPair_centers (family P) h.generate hc).1
  have hvw := Z_le_stabilizer_of_dist_le_b (family P) h.generate v w hc.1.le
  have hVuV := graph_V_adjacent_le (P := P) hu 1
  have hVv := (graph_V_le_Q_of_short h hS v hb).trans (Q_le_stabilizer _ _)
  have hVu := (graph_V_le_Q_of_short h hS u h1).trans (Q_le_stabilizer _ _)
  have hz : Z (family P) v ≠ ⊥ := by
    intro hz
    exact hne (by rw [hz, commutator_bot_left])
  exact source_radius_escape_of_common_normal_obstruction
    (stabilizer (family P) w) (stabilizer (family P) v) (stabilizer (family P) u)
    (Z (family P) v) (Z (family P) w) (V (family P) v 2) (V (family P) u 1)
    (graph_V_isPGroup_of_short h hS v hb)
    (hVv.trans (graph_Z_normalized h v)) (Z_le_V _ _ _)
    (hvw.trans (graph_Z_normalized h w)) (hwv.trans (graph_Z_normalized h v))
    (graph_Q_centralizes_Z h w) hSyl
    (le_iSup_of_le v (le_iSup_of_le ((mem_ball_one _ _ _).mpr (Or.inl hu.symm)) le_rfl))
    hVuV (le_inf (hVuV.trans hVv) hVu) hgen (graph_stabilizer_normalizes_V h u 1)
    hz (graph_common_normal_eq_bot h hu)

/-- Reverse escape moves an actual neighbor. Maximality of its relative point
stabilizer supplies the generating pair needed by (7.2). -/
theorem graph_exists_generating_neighbor (h : LocallyRankOneTriple P B)
    (hS : ∀ v, Stellmacher.IsSylowSubgroupIn (Q (family P) v) (U (family P) v))
    {v w : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v, Z (family P) w⁆ ≠ ⊥)
    (hmax : ∀ u, (graph (family P)).Adj v u →
      IsCoatom ((stabilizer (family P) u).subgroupOf (stabilizer (family P) v))) :
    ∃ u, (graph (family P)).Adj v u ∧
      Z (family P) w ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) u) =
        stabilizer (family P) v := by
  let := finite_endpoints h
  have hAv := (criticalPair_centers (family P) h.generate hc).1
  have hesc := (graph_criticalPair_reverse h hS hc hne).2
  have hex : ∃ u, (graph (family P)).Adj v u ∧ ¬ Z (family P) w ≤ stabilizer (family P) u := by
    by_contra! he
    apply hesc
    intro z hz u hu
    rcases (mem_ball_one (family P) v u).mp hu with hu | rfl
    · exact he u hu hz
    · exact hAv hz
  obtain ⟨u,hu,hAu⟩ := hex
  let H := stabilizer (family P) v
  let K := stabilizer (family P) u
  let A := Z (family P) w
  let D := A ⊔ (H ⊓ K)
  have hDH : D ≤ H := sup_le hAv inf_le_left
  have hle : K.subgroupOf H ≤ D.subgroupOf H := fun x hx => (show H ⊓ K ≤ D from le_sup_right) ⟨x.property,hx⟩
  have hne' : D.subgroupOf H ≠ K.subgroupOf H := by
    intro he
    apply hAu
    intro x hx
    have hm : (⟨x,hAv hx⟩ : H) ∈ D.subgroupOf H := (show A ≤ D from le_sup_left) hx
    rw [he] at hm
    exact hm
  have he := (hmax u hu).ne_iff_eq_top hle |>.mp hne'
  refine ⟨u,hu,?_⟩
  change D = H
  have hm := congrArg (Subgroup.map H.subtype) he
  rw [map_subgroupOf_eq_of_le hDH, ← MonoidHom.range_eq_map, range_subtype] at hm
  exact hm

/-- Radius-two escape from the genuine local maximal-edge premise, with the
generating neighbor constructed rather than assumed. -/
theorem graph_radius_two_escape_of_maximal_edges (h : LocallyRankOneTriple P B)
    (hS : ∀ v, Stellmacher.IsSylowSubgroupIn (Q (family P) v) (U (family P) v))
    {v w : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v, Z (family P) w⁆ ≠ ⊥)
    (hb : 2 < b (family P))
    (hSyl : Stellmacher.IsSylowSubgroupIn
      (Z (family P) v ⊔ Q (family P) w) (stabilizer (family P) w))
    (hmax : ∀ u, (graph (family P)).Adj v u →
      IsCoatom ((stabilizer (family P) u).subgroupOf (stabilizer (family P) v))) :
    ¬ V (family P) v 2 ≤ stabilizer (family P) w := by
  obtain ⟨u,hu,hgen⟩ := graph_exists_generating_neighbor h hS hc hne hmax
  exact graph_radius_two_escape h hS hc hne hb hu hSyl hgen

/-- Radius-one escape with local maximality and the earlier (6.6) obstruction. -/
theorem graph_radius_one_escape_of_maximal_edges (h : LocallyRankOneTriple P B)
    (hS : ∀ v, Stellmacher.IsSylowSubgroupIn (Q (family P) v) (U (family P) v))
    {v w : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v, Z (family P) w⁆ ≠ ⊥)
    (hb : 2 < b (family P))
    (hSyl : Stellmacher.IsSylowSubgroupIn
      (Z (family P) v ⊔ Q (family P) w) (stabilizer (family P) w))
    (hmax : ∀ u, (graph (family P)).Adj v u →
      IsCoatom ((stabilizer (family P) u).subgroupOf (stabilizer (family P) v)))
    (hobs : ∀ u, (graph (family P)).Adj v u → ¬ stabilizer (family P) v ≤
      normalizer ((Z (family P) u ⊔ Z (family P) v : Subgroup G) : Set G)) :
    ¬ V (family P) v 1 ≤ stabilizer (family P) w := by
  obtain ⟨u,hu,hgen⟩ := graph_exists_generating_neighbor h hS hc hne hmax
  exact graph_radius_one_escape h hS hc hb hu hSyl hgen (hobs u hu)


end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
