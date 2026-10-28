module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.PathControl
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.NaturalEndpoints

/-!
# The epsilon-one distance exclusion

Starting with a noncommuting critical pair, the radius-one escape gives a
noncommuting neighbor paired with the penultimate path vertex. Applying the
same escape there supplies a second neighbor. The two local rank-one
generation steps normalize the original nonzero critical commutator in
adjacent actors. Their full-edge coset covers contradict faithfulness.

The earlier local generation statements and the (7.1) Sylow products remain
explicit in this interface. `RadiusOneSource` supplies local generation
from marked rank-one quotients and applies the result to the actual reduced
graph. The epsilon-two branch and the recognition input are not proved here.
Source: DGS, *Groups and Graphs* (1985), (7.3), printed pp.127--128.
-/

public section
open Subgroup
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Escape of a radius-one group is witnessed by a genuine neighboring center. -/
theorem graph_exists_neighbor_escape
    {v w : Vertex (family P)}
    (hZ : Z (family P) v ≤ stabilizer (family P) w)
    (hV : ¬ V (family P) v 1 ≤ stabilizer (family P) w) :
    ∃ u, (graph (family P)).Adj v u ∧ ¬ Z (family P) u ≤ stabilizer (family P) w := by
  by_contra! hn
  apply hV
  apply iSup_le
  intro u
  apply iSup_le
  intro hu
  rcases (mem_ball_one (family P) v u).mp hu with hu | rfl
  · exact hn u hu
  · exact hZ

/-- If a short radius-one group escapes the next edge, the preceding
centralizer-Sylow property produces a new noncommuting critical pair. -/
theorem graph_exists_neighbor_noncommuting (h : LocallyRankOneTriple P B)
    (hS : ∀ v, Stellmacher.IsSylowSubgroupIn (Q (family P) v) (U (family P) v))
    {v t w : Vertex (family P)} (htw : (graph (family P)).Adj t w)
    (hshort : (graph (family P)).dist v t < b (family P))
    (hb : 1 < b (family P)) (L : Subgroup G) (hLP : L ≤ stabilizer (family P) t)
    (hVL : V (family P) v 1 ≤ L)
    (hVw : ¬ V (family P) v 1 ≤ stabilizer (family P) w)
    (hCS : Stellmacher.IsSylowSubgroupIn (Q (family P) t)
      (L ⊓ centralizer (Z (family P) t : Set G))) :
    ∃ u, (graph (family P)).Adj v u ∧ ⁅Z (family P) u,Z (family P) t⁆ ≠ ⊥ := by
  by_contra! hn
  have hVC : V (family P) v 1 ≤ centralizer (Z (family P) t : Set G) := by
    apply iSup_le
    intro u
    apply iSup_le
    intro hu
    rcases (mem_ball_one (family P) v u).mp hu with hu | rfl
    · exact commutator_eq_bot_iff_le_centralizer.mp (hn u hu)
    · exact graph_centers_commute_of_short h hS hshort
  have hQN : Q (family P) t ≤ L ⊓ centralizer (Z (family P) t : Set G) := by
    obtain ⟨S,hS⟩ := hCS
    rw [← hS]
    exact map_subtype_le _
  have hnQ : L ⊓ centralizer (Z (family P) t : Set G) ≤
      normalizer (Q (family P) t : Set G) :=
    (inf_le_left.trans hLP).trans ((stabilizer (family P) t).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have he := inf_eq_inf_of_normal_sylow (V (family P) v 1) _ _
    (graph_V_isPGroup_of_short h hS v hb) hQN hnQ hCS
  rw [inf_of_le_left (le_inf hVL hVC)] at he
  exact hVw ((he.le.trans inf_le_right).trans
    ((source_Z_Q_U h t).2.trans ((ballKernel_one_le_edge (family P) htw).trans inf_le_right)))

/-- The original critical commutator is normalized by the actual preceding
edge two-core. This uses the opposite-center Sylow product, not a replacement
of the local kernel by its two-core. -/
theorem graph_preceding_edge_normalizes_commutator (h : LocallyRankOneTriple P B)
    (hS : ∀ v, Stellmacher.IsSylowSubgroupIn (Q (family P) v) (U (family P) v))
    {v w t : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (htw : (graph (family P)).Adj t w)
    (hshort : (graph (family P)).dist v t < b (family P))
    (hprod : Stellmacher.IsSylowSubgroupIn (Z (family P) v ⊔ Q (family P) w)
      (stabilizer (family P) w)) :
    (stabilizer (family P) t ⊓ stabilizer (family P) w).pCoreIn 2 ≤
      normalizer ((⁅Z (family P) v,Z (family P) w⁆ : Subgroup G) : Set G) := by
  let := finite_endpoints h
  let T := (stabilizer (family P) t ⊓ stabilizer (family P) w).pCoreIn 2
  have hZT : Z (family P) v ≤ T :=
    (graph_Z_le_Q_of_short h hS hshort).trans (graph_Q_le_edgeCore h htw)
  have hQT : Q (family P) w ≤ T := by
    simpa only [T,inf_comm] using graph_Q_le_edgeCore h htw.symm
  have he : Z (family P) v ⊔ Q (family P) w = T :=
    sylow_join_eq_of_le _ _ _ _ hprod (isPGroup_pCoreIn 2 _)
      ((pCoreIn_le 2 _).trans inf_le_right) hZT hQT
  have hNZ : Z (family P) v ≤ normalizer (Z (family P) w : Set G) :=
    (Z_le_stabilizer_of_dist_le_b (family P) h.generate v w hc.1.le).trans
      ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ _)).mp (Z_normal _ _))
  have hcomm : ⁅Z (family P) v,Z (family P) w⁆ = ⁅T,Z (family P) w⁆ := by
    simpa only [commutator_comm (Z (family P) w)] using
      commutator_eq_of_centralizing_sup (by rw [sup_comm]; exact he)
        (graph_Q_centralizes_Z h w) hNZ
  rw [hcomm]
  exact normalizer_commutator_ge_left _ _

/-- The epsilon-one distance argument of DGS (7.3). The inputs are the
prior (7.1) Sylow products, (6.6) center-product obstruction, and the literal
local generation/cover statements of (5.1),(6.0). The proof constructs both
new centers, both generation steps, and the common-normal contradiction. -/
theorem graph_radiusOne_distance_bound (h : LocallyRankOneTriple P B)
    (hS : ∀ v, Stellmacher.IsSylowSubgroupIn (Q (family P) v) (U (family P) v))
    (L : Vertex (family P) → Subgroup G)
    (hL : ∀ v, L v ≤ stabilizer (family P) v)
    (hcover : ∀ v w, (graph (family P)).Adj v w →
      ∀ a ∈ stabilizer (family P) v, ∃ l ∈ L v,
        ∃ t ∈ stabilizer (family P) v ⊓ stabilizer (family P) w, a = l*t)
    (hEL : ∀ v w, (graph (family P)).Adj v w →
      (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 ≤ L v)
    (hgen : ∀ v w, (graph (family P)).Adj v w → ∀ A : Subgroup G,
      IsPGroup 2 A → A ≤ stabilizer (family P) v → ¬ A ≤ stabilizer (family P) w →
      A ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 = L v)
    (hprod : ∀ v w, IsCriticalPair (family P) v w → ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥ →
      Stellmacher.IsSylowSubgroupIn (Z (family P) v ⊔ Q (family P) w) (stabilizer (family P) w))
    (hobs : ∀ v u, (graph (family P)).Adj v u → ¬ stabilizer (family P) v ≤
      normalizer ((Z (family P) u ⊔ Z (family P) v : Subgroup G) : Set G))
    (hCS : ∀ v, Stellmacher.IsSylowSubgroupIn (Q (family P) v)
      (L v ⊓ centralizer (Z (family P) v : Set G)))
    {v w : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥) : b (family P) ≤ 2 := by
  let := finite_endpoints h
  by_contra! hb
  have h1 : 1 < b (family P) := by omega
  have hescape {x y : Vertex (family P)} (hc : IsCriticalPair (family P) x y)
      (hn : ⁅Z (family P) x,Z (family P) y⁆ ≠ ⊥) :
      ¬ V (family P) x 1 ≤ stabilizer (family P) y :=
    graph_radius_one_escape_of_maximal_edges h hS hc hn hb (hprod x y hc hn)
      (fun _ hu => graph_edge_isCoatom h hu) (hobs x)
  have hvw : v ≠ w := by
    intro he
    have hd := hc.1
    rw [he,SimpleGraph.dist_self] at hd
    omega
  obtain ⟨t,hwt,ht⟩ := exists_predecessor (family P) h.generate v w hvw
  have hvt : v ≠ t := by
    intro he
    rw [← he,SimpleGraph.dist_self,hc.1] at ht
    omega
  obtain ⟨s,hts,hs⟩ := exists_predecessor (family P) h.generate v t hvt
  have hshort : (graph (family P)).dist v t < b (family P) := by rw [hc.1] at ht; omega
  have hVt := graph_V_le_stabilizer_of_distance h (v := v) (w := t) (i := 1)
    (by rw [ht,hc.1])
  have hVw := hescape hc hne
  have hLt := hgen t w hwt.symm (V (family P) v 1)
    (graph_V_isPGroup_of_short h hS v h1) hVt hVw
  let R := ⁅Z (family P) v,Z (family P) w⁆
  have hVR : V (family P) v 1 ≤ normalizer (R : Set G) :=
    (commutator_eq_bot_iff_le_centralizer.mp
      (graph_V_centralizes_commutator h hS hc h1)).trans (Subgroup.centralizer_le_normalizer _)
  have hLtR : L t ≤ normalizer (R : Set G) := by
    rw [← hLt]
    exact sup_le hVR (graph_preceding_edge_normalizes_commutator h hS hc hwt.symm
      hshort (hprod v w hc hne))
  obtain ⟨u,hvu,hut⟩ := graph_exists_neighbor_noncommuting h hS hwt.symm hshort h1
    (L t) (hL t) (hLt ▸ le_sup_left) hVw (hCS t)
  have hdut : (graph (family P)).dist u t ≤ b (family P) := by
    have htri := (connected_graph h).dist_triangle (u := u) (v := v) (w := t)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hvu.symm] at htri
    rw [hc.1] at ht
    omega
  have hcut := graph_critical_of_noncommuting h hS hdut hut
  obtain ⟨r,hur,hrt⟩ := graph_exists_neighbor_escape
    (Z_le_stabilizer_of_dist_le_b (family P) h.generate u t hdut) (hescape hcut hut)
  have hdvr : (graph (family P)).dist v r ≤ 2 := by
    have hh := (connected_graph h).dist_triangle (u := v) (v := u) (w := r)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hvu,SimpleGraph.dist_eq_one_iff_adj.mpr hur] at hh
    exact hh
  have hdrs : (graph (family P)).dist r s ≤ b (family P) := by
    have hh := (connected_graph h).dist_triangle (u := r) (v := v) (w := s)
    rw [SimpleGraph.dist_comm (u := r) (v := v)] at hh
    rw [hc.1] at ht
    omega
  let := graph_Z_elementary h r
  have hLs := hgen s t hts.symm (Z (family P) r) (IsElementaryAbelian.isPGroup 2 _)
    (Z_le_stabilizer_of_dist_le_b (family P) h.generate r s hdrs) hrt
  have hZR : Z (family P) r ≤ normalizer (R : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    apply (graph_centers_commute_of_short h hS (v := r) (w := v) ?_).trans
    · exact centralizer_le ((criticalPair_centers (family P) h.generate hc).2.trans inf_le_left)
    · rw [SimpleGraph.dist_comm]
      omega
  have hLsR : L s ≤ normalizer (R : Set G) := by
    rw [← hLs]
    refine sup_le hZR ?_
    have he : (stabilizer (family P) s ⊓ stabilizer (family P) t).pCoreIn 2 ≤ L t := by
      simpa only [inf_comm] using hEL t s hts
    exact he.trans hLtR
  have hRv : R ≤ Z (family P) v := (criticalPair_centers (family P) h.generate hc).2.trans inf_le_left
  have hRE : R ≤ stabilizer (family P) s ⊓ stabilizer (family P) t := by
    refine le_inf (hRv.trans ?_) (hRv.trans ?_)
    · apply Z_le_stabilizer_of_dist_le_b (family P) h.generate
      rw [hc.1] at ht
      omega
    · exact Z_le_stabilizer_of_dist_le_b (family P) h.generate v t hshort.le
  apply hne
  apply graph_local_common_normal_eq_bot h hts.symm (L s) (L t) R
    (hcover s t hts.symm) ?_ hRE hLsR hLtR
  intro a ha
  simpa only [inf_comm] using hcover t s hts a ha

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
