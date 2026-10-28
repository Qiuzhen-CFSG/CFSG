module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicNeighborSeeds
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicTerminalIntersection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicTerminalIndex

/-!
# Constructing the intrinsic terminal quotient marking

The actual neighbor seeds transport along the critical orbit. Their splitting
and the intrinsic centralizer-Sylow alternative put the radius-two span in
the penultimate even core. For an escaping neighboring radius-one actor,
the proved intersection normality and the existing root-and-mover action
supply the radius-index comparison. Natural fixed lines make the terminal
intersection centralize that actor. The intrinsic module estimate therefore
forces the terminal quotient to be linear.

Every core, centralizer, actor and quotient in this argument is the literal
reduced F.1.1 object. No model on the opposite orbit is assumed. These are
the setup premises used in `IntrinsicNoncommutingBound` to invoke the
already proved Chapter 7 distance implication.
Source: DGS, *Groups and Graphs* (1985), (7.5)(1)--(3) and its final
radius/core comparison, pp.129--131; corrected (5.12).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open Noncommuting
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))

/-- Transport the constructed natural seeds along the actual critical orbit. -/
theorem reduced_long_neighbor_centers_split_of_type (h : HypothesisF11 L S)
    {v w y a c : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : 2 < b F) (htype : v.type = y.type)
    (hya : (graph F).Adj y a) (hyc : (graph F).Adj y c) (hac : a ≠ c) :
    Z F y = Z F a ⊔ Z F c ∧ Disjoint (Z F a) (Z F c) := by
  let : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  obtain ⟨g,rfl⟩ := (same_orbit_iff F v y).mpr htype
  have ha : (graph F).Adj v (g⁻¹ • a) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g⁻¹).map_adj_iff.mpr hya
    change (graph F).Adj (g⁻¹ • (g • v)) (g⁻¹ • a) at hh
    simpa only [inv_smul_smul] using hh
  have hc' : (graph F).Adj v (g⁻¹ • c) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g⁻¹).map_adj_iff.mpr hyc
    change (graph F).Adj (g⁻¹ • (g • v)) (g⁻¹ • c) at hh
    simpa only [inv_smul_smul] using hh
  have hne' : g⁻¹ • a ≠ g⁻¹ • c := fun he => hac ((MulAction.injective g⁻¹) he)
  obtain ⟨hspan,hdis⟩ := reduced_long_neighbor_centers_split h hc hne hb ha hc' hne'
  constructor
  · have he := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hspan
    simpa only [Subgroup.map_sup,←Z_translate,smul_inv_smul] using he
  · have he := Subgroup.disjoint_map (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective hdis
    simpa only [←Z_translate,smul_inv_smul] using he

/-- The radius-two span lies in the literal penultimate even core. -/
theorem reduced_long_terminal_core_containment (h : HypothesisF11 L S)
    {v w t y x : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : 2 < b F) (hwt : (graph F).Adj w t)
    (hty : (graph F).Adj t y) (hyx : (graph F).Adj y x)
    (hdt : (graph F).dist v t + 1 = b F)
    (hdy : (graph F).dist v y + 1 = (graph F).dist v t)
    (hdx : (graph F).dist v x + 1 = (graph F).dist v y) :
    V F v 2 ≤ Q F y := by
  let ht := reduced_triple h
  let := finite_endpoints ht
  let : ∀ i, Finite (F i) := finite_endpoints ht
  have hp := graph_V_isPGroup_of_short ht (reduced_kernel_sylow h) v hb
  have hVL : V F v 2 ≤ graphLocalGroup F y :=
    pGroup_le_sylowGenerated _ _ (graph_V_le_stabilizer_of_distance ht (by omega)) hp
  let := graph_Z_elementary ht w
  have hZW : Z F w ≤ graphLocalGroup F v :=
    pGroup_le_sylowGenerated _ _
      (Z_le_stabilizer_of_dist_le_b F ht.generate w v (by rw [SimpleGraph.dist_comm,hc.1]))
      (IsElementaryAbelian.isPGroup 2 _)
  have hvw := (same_orbit_iff F v w).mp (reduced_long_critical_even h hc hne hb).1
  have hwy : w.type = y.type := by
    have h₁ := hwt.1
    have h₂ := hty.1
    cases hw : w.type <;> cases ht : t.type <;> cases hy : y.type <;> simp_all
  have hvy := hvw.trans hwy
  have hxt : x ≠ t := by
    intro he
    rw [he] at hdx
    omega
  have hs := reduced_long_neighbor_centers_split_of_type h hc hne hb hvy hyx hty.symm hxt
  have hrev := (reduced_noncommuting_critical_intersections h hc hne).1
  have hid := (reduced_long_critical_forward_identities h hrev
    (by rwa [commutator_comm]) hb hwt (by rwa [SimpleGraph.dist_comm])).1
  rw [commutator_comm] at hid
  have hCx : V F v 2 ≤ centralizer (Z F x : Set (G₀ L S)) :=
    (graph_V_le_Q_of_distance ht (reduced_kernel_sylow h) (by omega)).trans
      (graph_Q_centralizes_Z ht x)
  have hCt : V F v 2 ≤ centralizer (Z F t : Set (G₀ L S)) := by
    rw [←hid]
    exact commutator_eq_bot_iff_le_centralizer.mp
      (graph_V_centralizes_commutator ht (reduced_kernel_sylow h) hc hb)
  have hCy : V F v 2 ≤ centralizer (Z F y : Set (G₀ L S)) := by
    rw [le_centralizer_iff,hs.1]
    exact sup_le (le_centralizer_iff.mp hCx) (le_centralizer_iff.mp hCt)
  have hCS := (graph_intrinsic_centralizer_dichotomy ht (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) y).resolve_right (fun he =>
      center_ne_omega_of_noncommuting (graphLocalGroup F v) _ _ hZW hne
        ((graph_center_equality_of_type ht (graphLocalGroup F) (graphLocalGroup_conjugate ht) hvy).mpr he))
  have hQN : Q F y ≤ graphLocalGroup F y ⊓ centralizer (Z F y : Set (G₀ L S)) := by
    obtain ⟨T,hT⟩ := hCS
    rw [←hT]
    exact map_subtype_le _
  have hnQ : graphLocalGroup F y ⊓ centralizer (Z F y : Set (G₀ L S)) ≤
      normalizer (Q F y : Set (G₀ L S)) :=
    (inf_le_left.trans (sylowGenerated_le _)).trans ((stabilizer F y).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have he := inf_eq_inf_of_normal_sylow (V F v 2) _ _ hp hQN hnQ hCS
  rw [inf_of_le_left (le_inf hVL hCy)] at he
  exact he.le.trans inf_le_right

/-- The terminal intersection argument constructs the opposite linear quotient. -/
theorem reduced_long_terminal_linear (h : HypothesisF11 L S)
    {v w u t a y x : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : 4 < b F) (hvu : (graph F).Adj v u) (hwt : (graph F).Adj w t)
    (hva : (graph F).Adj v a) (hua : u ≠ a)
    (hdu : (graph F).dist u w + 1 = b F) (hdt : (graph F).dist v t + 1 = b F)
    (hty : (graph F).Adj t y) (hyx : (graph F).Adj y x)
    (hdx : (graph F).dist v x + 3 = b F)
    (hcore : V F v 2 ≤ Q F y) (hesc : ¬ V F a 1 ≤ Q F t) :
    ∃ n, 0 < n ∧ ClassicalGroup.IsPSL
      (graphLocalGroup F t ⧸ pCore 2 (graphLocalGroup F t)) 2 (2^n) := by
  let ht := reduced_triple h
  let := finite_endpoints ht
  let : ∀ i, Finite (F i) := finite_endpoints ht
  have hs := reduced_long_neighbor_centers_split h hc hne (by omega) hvu hva hua
  have hid := reduced_long_critical_forward_identities h hc hne (by omega) hvu hdu
  have huc : Z F w ≤ centralizer (Z F u : Set (G₀ L S)) :=
    graph_centers_commute_of_short ht (reduced_kernel_sylow h)
      (by rw [SimpleGraph.dist_comm]; omega)
  have hm := graph_critical_center_moves_other_neighbor ht hs.1 hs.2 hid.1 huc hne
  have hK := reduced_long_radius_core_intersection_le_neighbors h hc hne (by omega) hva hwt hdt hm
  have hrev := (reduced_noncommuting_critical_intersections h hc hne).1
  have hit := reduced_long_critical_forward_identities h hrev (by rwa [commutator_comm])
    (by omega) hwt (by rwa [SimpleGraph.dist_comm])
  let := graph_Z_elementary ht w
  have hZW : Z F w ≤ graphLocalGroup F v := pGroup_le_sylowGenerated _ _
    (Z_le_stabilizer_of_dist_le_b F ht.generate w v (by rw [SimpleGraph.dist_comm,hc.1]))
    (IsElementaryAbelian.isPGroup 2 _)
  have hZesc : ¬ Z F w ≤ Q F v := by
    intro hh
    exact hne (commutator_comm _ _ |>.trans
      (commutator_eq_bot_iff_le_centralizer.mpr (hh.trans (graph_Q_centralizes_Z ht v))))
  have hf := natural_center_fixed_eq_commutator (graphLocalGroup F v) (Z F v)
    (Q F v) (Z F w) (reduced_critical_natural_centers_and_products h hc hne).1
    (reduced_long_critical_center_trivial h hc hne (by omega) hvu) hZW
    (IsElementaryAbelian.isPGroup 2 _) hZesc
  rw [hid.1] at hf
  have hdis : Z F a ⊓ Q F w = ⊥ := by
    apply bot_unique
    rw [←disjoint_iff.mp hs.2]
    exact le_inf ((le_inf (inf_le_left.trans (hs.1 ▸ le_sup_right))
      (inf_le_right.trans (graph_Q_centralizes_Z ht w))).trans hf.le) inf_le_left
  have hua' : u.type = a.type := by
    have hu := hvu.1
    have ha := hva.1
    cases hv : v.type <;> cases hu' : u.type <;> cases ha' : a.type <;> simp_all
  have htx : t.type = x.type := by
    have ht := hty.1
    have hx := hyx.1
    cases ht' : t.type <;> cases hy : y.type <;> cases hx' : x.type <;> simp_all
  have hAa := graph_radius_commutator_of_type ht hua' hid.2.1
  have hXx := graph_radius_commutator_of_type ht htx hit.2.1
  have hav : (graph F).dist a v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hva.symm
  have hax := (connected_graph ht).dist_triangle (u := a) (v := v) (w := x)
  have hAX : V F a 1 ≤ Q F x := graph_V_le_Q_of_distance ht (reduced_kernel_sylow h) (by omega)
  have hXA : V F x 1 ≤ Q F a :=
    graph_V_le_Q_of_distance ht (reduced_kernel_sylow h) (by rw [SimpleGraph.dist_comm]; omega)
  have hxy : (graph F).dist x y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hyx.symm
  have hyt : (graph F).dist y t = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hty.symm
  have htw : (graph F).dist t w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hwt.symm
  have hxw : (graph F).dist x w < b F := by
    have h₁ := (connected_graph ht).dist_triangle (u := x) (v := y) (w := t)
    have h₂ := (connected_graph ht).dist_triangle (u := x) (v := t) (w := w)
    omega
  have hcomm : ⁅V F a 1,V F t 1 ⊓ V F x 1⁆ = ⊥ := by
    apply bot_unique
    rw [←hdis]
    apply le_inf
    · exact (commutator_mono le_rfl (inf_le_right.trans hXA)).trans hAa.le
    · have he : ⁅V F a 1,V F t 1 ⊓ V F x 1⁆ ≤ Z F x := by
        rw [commutator_comm]
        exact (commutator_mono inf_le_right hAX).trans hXx.le
      exact he.trans (graph_Z_le_Q_of_short ht (reduced_kernel_sylow h) hxw)
  have hC : V F t 1 ⊓ V F x 1 ≤ centralizer (V F a 1 : Set (G₀ L S)) := by
    rw [commutator_comm] at hcomm
    exact commutator_eq_bot_iff_le_centralizer.mp hcomm
  let : Finite (V F a 1) := Finite.of_injective
    (inclusion ((graph_V_le_Q_of_short ht (reduced_kernel_sylow h) a (by omega : 1 < b F)).trans
      (pCoreIn_le 2 _))) (inclusion_injective _)
  let : Finite (V F t 1) := Finite.of_injective
    (inclusion ((graph_V_le_Q_of_short ht (reduced_kernel_sylow h) t (by omega : 1 < b F)).trans
      (pCoreIn_le 2 _))) (inclusion_injective _)
  have hvw := (same_orbit_iff F v w).mp (reduced_long_critical_even h hc hne (by omega)).1
  have hvy : v.type = y.type := by
    have hw := hwt.1
    have hy := hty.1
    cases hv : v.type <;> cases hw' : w.type <;> cases ht' : t.type <;>
      cases hy' : y.type <;> simp_all
  apply (reduced_long_terminal_actor_index h hc hne hb hwt hdt hty hcore
    (V F a 1) (graph_V_adjacent_le hva 1) hesc).2
  calc
    _ ≤ (V F t 1 ⊓ V F x 1).relIndex (V F t 1) :=
      relIndex_le_of_le_left hC index_ne_zero_of_finite
    _ = (V F x 1).relIndex (V F t 1) := inf_relIndex_left _ _
    _ ≤ (V F a 1 ⊓ Q F t).relIndex (V F a 1) :=
      graph_radius_intersection_index_transport ht hva hty.symm hyx hvy _ hK
    _ = (Q F t).relIndex (V F a 1) := inf_relIndex_left _ _

end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
