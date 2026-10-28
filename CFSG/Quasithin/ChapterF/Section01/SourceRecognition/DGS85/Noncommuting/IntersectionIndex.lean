module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.RootCoreAction

/-!
# Transporting the final radius/core index

The intersection V_(alpha-1) ∩ Q_(alpha-prime-1) is normalized by the
opposite core and critical center. Their proved transitive local action
places this intersection in every neighboring radius-one span. Transport
along an oriented edge then bounds the terminal radius intersection index
by the original actor image order. The proof needs no identification of
that order with the defining-field parameter.

Source: DGS, *Groups and Graphs* (1985), (7.5), printed pp.130--131.
-/

public noncomputable section
open Subgroup
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

theorem graph_normalized_radius_intersection_le_neighbors
    (h : LocallyRankOneTriple P B)
    {v a : Vertex (family P)} (H K : Subgroup G)
    (hK : K ≤ V (family P) a 1) (hn : H ≤ normalizer (K : Set G))
    (ht : ∀ x, (graph (family P)).Adj v x → ∃ g ∈ H, g • a = x) :
    ∀ x, (graph (family P)).Adj v x → K ≤ V (family P) x 1 := by
  let := finite_endpoints h
  intro x hx
  obtain ⟨g,hg,rfl⟩ := ht x hx
  rw [V_translate]
  have he := mem_normalizer_iff_map_conj_eq.mp (hn hg)
  exact he.symm.le.trans (map_mono hK)

theorem graph_epsilonTwo_radius_core_intersection
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (L : Vertex (family P) → Subgroup G)
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (d : ∀ x y, (graph (family P)).Adj x y →
      LocalRankOneData (stabilizer (family P) x)
        (stabilizer (family P) x ⊓ stabilizer (family P) y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer (family P) x))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x)
      (L x ⊓ centralizer (Z (family P) x : Set G)) ∨
      Z (family P) x = Stellmacher.omegaOneCenterAmbient (L x))
    (hob : ∀ x y, (graph (family P)).Adj x y → ¬ stabilizer (family P) y ≤ normalizer
      ((Q (family P) x ⊓ Q (family P) y : Subgroup G) : Set G))
    {v w u t a : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥)
    (hvu : (graph (family P)).Adj v u) (hwt : (graph (family P)).Adj w t)
    (hva : (graph (family P)).Adj v a) (hua : u ≠ a)
    (hdu : (graph (family P)).dist u w + 1 = b (family P))
    (hdt : (graph (family P)).dist v t + 1 = b (family P))
    (hepsilon : Z (family P) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2))
    (hnat₀ : HasNaturalCenter (L v) (Z (family P) v) (Q (family P) v))
    (hnat₁ : HasNaturalCenter (L w) (Z (family P) w) (Q (family P) w))
    (hsyl : Stellmacher.IsSylowSubgroupIn
      (Z (family P) v ⊔ Q (family P) w) (stabilizer (family P) w))
    (hb : 2 < b (family P)) :
    ∀ x, (graph (family P)).Adj v x →
      V (family P) a 1 ⊓ Q (family P) t ≤ V (family P) x 1 := by
  let := finite_endpoints h
  let A := V (family P) a 1
  let K := A ⊓ Q (family P) t
  have hsplit := graph_epsilonTwo_centers_split_of_type h hB L d hstar hodd hdich
    hvu hepsilon hnat₀ rfl hvu hva hua
  have hR := (graph_epsilonTwo_critical_centers h hB hS L hcov d hstar hodd hdich hob
    hc hne hvu hwt hdu hdt hepsilon hnat₀ hnat₁).1
  have huc : Z (family P) w ≤ centralizer (Z (family P) u : Set G) :=
    graph_centers_commute_of_short h hS (by rw [SimpleGraph.dist_comm]; omega)
  have hm := graph_critical_center_moves_other_neighbor h hsplit.1 hsplit.2 hR huc hne
  have hAv : A ≤ stabilizer (family P) v :=
    graph_V_le_stabilizer_of_distance h (by rw [SimpleGraph.dist_comm,
      SimpleGraph.dist_eq_one_iff_adj.mpr hva]; omega)
  have hZWv : Z (family P) w ≤ stabilizer (family P) v :=
    Z_le_stabilizer_of_dist_le_b (family P) h.generate w v
      (by rw [SimpleGraph.dist_comm,hc.1])
  have ht : ∀ x, (graph (family P)).Adj v x →
      ∃ g ∈ Q (family P) a ⊔ Z (family P) w, g • a = x := by
    intro x hx
    exact graph_core_and_mover_transitive h hB hva (d v a hva)
      (by rw [hstar]; exact hodd v) (by rw [hstar]; exact hnat₀)
      (hob v a hva) _ hZWv hm hx
  have hZvA : Z (family P) v ≤ A :=
    le_iSup_of_le v (le_iSup_of_le ((mem_ball_one _ _ _).mpr (Or.inl hva.symm)) le_rfl)
  have hZvK : Z (family P) v ≤ K := le_inf hZvA (graph_Z_le_Q_of_short h hS (by omega))
  have hcenter : center (L v) = ⊥ := by
    rw [←hstar v u hvu]
    exact graph_epsilonTwo_center_trivial_of_localData h hB hvu (d v u hvu) (d u v hvu.symm)
      (by rw [hstar]; exact hodd v) (by rw [hstar]; exact hodd u)
      (by rw [hstar]; exact hdich u) hepsilon
  have hQaesc : ¬ Q (family P) a ≤ Q (family P) v := by
    intro he
    apply hob v a hva
    rw [inf_eq_right.mpr he]
    exact (stabilizer (family P) a).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hQa : ⁅Z (family P) v,Q (family P) a⁆ = Z (family P) a := by
    rw [graph_epsilonTwo_at_neighbor h hvu hva hepsilon]
    exact graph_natural_edge_commutator h hB hva (d v a hva)
      (by rw [hstar]; exact hodd v) (by rw [hstar]; exact hcenter)
      (by rw [hstar]; exact hnat₀) _
      (by simpa only [inf_comm] using graph_Q_le_edgeCore h hva.symm) hQaesc
  have hAQa := graph_radius_one_commutator_of_edge h hva hQa
  have hQaK : Q (family P) a ≤ normalizer (K : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact ((commutator_mono inf_le_left le_rfl).trans hAQa.le).trans
      ((hsplit.1 ▸ le_sup_right).trans hZvK)
  have hZvN : stabilizer (family P) v ≤ normalizer (Z (family P) v : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ _)).mp (Z_normal _ _)
  have hZwN : stabilizer (family P) w ≤ normalizer (Z (family P) w : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ _)).mp (Z_normal _ _)
  have hZvZw : Z (family P) v ≤ normalizer (Z (family P) w : Set G) :=
    (Z_le_stabilizer_of_dist_le_b (family P) h.generate v w hc.1.le).trans hZwN
  have hKw : K ≤ stabilizer (family P) w :=
    (inf_le_right.trans (source_Z_Q_U h t).2).trans
      ((ballKernel_one_le_edge (family P) hwt.symm).trans inf_le_right)
  have hRK : ⁅Z (family P) v,Z (family P) w⁆ ≤ K :=
    (le_normalizer_iff_commutator_le_left.mp (hZWv.trans hZvN)).trans hZvK
  have hZwK : Z (family P) w ≤ normalizer (K : Set G) :=
    (source_radius_commutator (stabilizer (family P) w) (Z (family P) v)
      (Z (family P) w) K ((graph_V_isPGroup_of_short h hS a (by omega : 1 < b (family P))).to_le inf_le_left)
      ((inf_le_left.trans hAv).trans hZvN) hZvK hKw hZvZw
      (graph_Q_centralizes_Z h w) hsyl).2.2 K hRK le_rfl
  exact graph_normalized_radius_intersection_le_neighbors h _ K inf_le_left
    (sup_le hQaK hZwK) ht

theorem graph_radius_intersection_index_transport
    (h : LocallyRankOneTriple P B)
    {v a y t x : Vertex (family P)}
    (hva : (graph (family P)).Adj v a) (hyt : (graph (family P)).Adj y t)
    (hyx : (graph (family P)).Adj y x) (htype : v.type = y.type)
    (K : Subgroup G) (hK : ∀ z, (graph (family P)).Adj v z → K ≤ V (family P) z 1)
    [Finite (V (family P) a 1)] :
    (V (family P) x 1).relIndex (V (family P) t 1) ≤ K.relIndex (V (family P) a 1) := by
  let := finite_endpoints h
  obtain ⟨g,hgv⟩ := (same_orbit_iff (family P) v y).mpr htype
  have hga : (graph (family P)).Adj y (g • a) := by
    have he := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hva
    change (graph (family P)).Adj (g • v) (g • a) at he
    rwa [hgv] at he
  obtain ⟨r,hr,hrt⟩ := locally_transitive (family P) hga hyt
  let f := r*g
  have hfv : f • v = y := by rw [show f = r*g from rfl,mul_smul,hgv]; exact hr
  have hfa : f • a = t := by rw [show f = r*g from rfl,mul_smul]; exact hrt
  have hpre : (graph (family P)).Adj v (f⁻¹ • x) := by
    have he := (Subgroup.CosetGeometry.translationGraphIso (family P) f⁻¹).map_adj_iff.mpr hyx
    change (graph (family P)).Adj (f⁻¹ • y) (f⁻¹ • x) at he
    rwa [←hfv,inv_smul_smul] at he
  have hm : K.map (MulAut.conj f).toMonoidHom ≤ V (family P) x 1 := by
    have he := map_mono (f := (MulAut.conj f).toMonoidHom) (hK _ hpre)
    rwa [←V_translate,smul_inv_smul] at he
  have hi : (K.map (MulAut.conj f).toMonoidHom).relIndex (V (family P) t 1) =
      K.relIndex (V (family P) a 1) := by
    rw [←hfa,V_translate]
    exact relIndex_map_map_of_injective _ _ (MulAut.conj f).injective
  exact hi ▸ relIndex_le_of_le_left hm (by rw [hi]; exact index_ne_zero_of_finite)

theorem graph_epsilonTwo_radius_index_comparison
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (L : Vertex (family P) → Subgroup G)
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (d : ∀ x y, (graph (family P)).Adj x y →
      LocalRankOneData (stabilizer (family P) x)
        (stabilizer (family P) x ⊓ stabilizer (family P) y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer (family P) x))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x)
      (L x ⊓ centralizer (Z (family P) x : Set G)) ∨
      Z (family P) x = Stellmacher.omegaOneCenterAmbient (L x))
    (hob : ∀ x y, (graph (family P)).Adj x y → ¬ stabilizer (family P) y ≤ normalizer
      ((Q (family P) x ⊓ Q (family P) y : Subgroup G) : Set G))
    {v w u t a y x : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥)
    (hvu : (graph (family P)).Adj v u) (hwt : (graph (family P)).Adj w t)
    (hva : (graph (family P)).Adj v a) (hua : u ≠ a)
    (hdu : (graph (family P)).dist u w + 1 = b (family P))
    (hdt : (graph (family P)).dist v t + 1 = b (family P))
    (hepsilon : Z (family P) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2))
    (hnat₀ : HasNaturalCenter (L v) (Z (family P) v) (Q (family P) v))
    (hnat₁ : HasNaturalCenter (L w) (Z (family P) w) (Q (family P) w))
    (hsyl : Stellmacher.IsSylowSubgroupIn
      (Z (family P) v ⊔ Q (family P) w) (stabilizer (family P) w))
    (hb : 2 < b (family P))
    (hty : (graph (family P)).Adj t y) (hyx : (graph (family P)).Adj y x) :
    (V (family P) x 1).relIndex (V (family P) t 1) ≤
      (Q (family P) t).relIndex (V (family P) a 1) := by
  let := finite_endpoints h
  let : Finite (V (family P) a 1) := Finite.of_injective
    (inclusion ((graph_V_le_Q_of_short h hS a (by omega : 1 < b (family P))).trans
      (pCoreIn_le 2 (stabilizer (family P) a)))) (inclusion_injective _)
  have hvw := (graph_epsilonTwo_even_of_localData h hB L hcov d hstar hodd hdich
    hc hne hvu hepsilon).1
  have htype : v.type = y.type := by
    have he := (same_orbit_iff (family P) v w).mp hvw
    have hw := hwt.1
    have hy := hty.1
    cases hv : v.type <;> cases hw' : w.type <;> cases ht : t.type <;>
      cases hy' : y.type <;> simp_all
  have hK := graph_epsilonTwo_radius_core_intersection h hB hS L hcov d hstar hodd hdich hob
    hc hne hvu hwt hva hua hdu hdt hepsilon hnat₀ hnat₁ hsyl hb
  have hi := graph_radius_intersection_index_transport h hva hty.symm hyx htype
    (V (family P) a 1 ⊓ Q (family P) t) hK
  rwa [inf_relIndex_left] at hi

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
