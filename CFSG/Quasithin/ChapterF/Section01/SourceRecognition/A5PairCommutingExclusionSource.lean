module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCommutingIntersectionSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearResidualLayer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualNaturalitySource

/-!
# Exclusion of the original commuting A5/A5 critical branch

The original A5 marks and actual critical geometry produce every required
Chapter 12 datum: common Sylows, center orders sixteen and four, natural-center
minimality, commutator identities, and the conjugated intersection indices.
The linear intersection theorem therefore constructs the natural quotient
of the terminal radius-one span by its center. The whole span has order 64.

Its middle center has order 16 and lies in both elementary radius-one spans.
It centralizes the opposite span, so the original centralizer index is at
most four. The genuine reciprocal critical configuration has full opposite
actor index four. Saturated residual recognition now constructs the entire
literal NaturalResidualSection, with its actual two-residual centralizer
and quotient action. DGS (8.5) excludes that section.

The last two theorems transport the based argument along the actual graph
edge and choose the first critical edge internally. Thus every original
critical pair has noncommuting centers. The full F.1.1 hypotheses, actual
original A5 marks, original inclusion and whole reduced Borel are retained.
No reduced comparison, catalogue, naturality, residual section, core equality,
containment, branch selector, or earlier source callback is supplied.

Source: DGS, Groups and Graphs (1985), (8.5)--(8.7), (12.1), (12.3)(a,c),
(12.4), printed pp.139--140,178--181.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open CFSG.Quasithin.ChapterF.Source CFSG.Quasithin.ChapterF.Source.DGS85
open CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
namespace CFSG.Quasithin.ChapterF.Source
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Original A5/A5 source consequence with all auxiliary data constructed internally. -/
theorem a5_pair_commuting_based_span_card
    (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    (i : Bool) {v u : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) v (base (Reduction.reducedFamily L S) (!i)))
    (hvu : (graph (Reduction.reducedFamily L S)).Adj v u)
    (hd : (graph (Reduction.reducedFamily L S)).dist u (base (Reduction.reducedFamily L S) (!i)) + 1 =
      b (Reduction.reducedFamily L S))
    (hcomm : ⁅Z (Reduction.reducedFamily L S) v, Z (Reduction.reducedFamily L S) (base (Reduction.reducedFamily L S) (!i))⁆ = ⊥)
    (hum : (graph (Reduction.reducedFamily L S)).Adj u (base (Reduction.reducedFamily L S) i)) :
    Nat.card (V (Reduction.reducedFamily L S) (base (Reduction.reducedFamily L S) (!i)) 1) = 64 := by
  let F := Reduction.reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let ht := Reduction.reduced_triple h
  let : ∀ j, Finite (F j) := finite_endpoints ht
  have hmy : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨hb3, _⟩ := a5_pair_commuting_critical_remaining h a hc hvu hd hcomm
  have hb : 2 < b F := by
    change 2 < b (Reduction.reducedFamily L S)
    omega
  have hne : u ≠ y := by
    intro he
    change (graph F).dist u y + 1 = b F at hd
    rw [he, SimpleGraph.dist_self] at hd
    omega
  have htm : v.type = m.type := (Bool.eq_not_of_ne hvu.1).trans
    (Bool.eq_not_of_ne hum.1.symm).symm
  have hc4 : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by decide)
  let e4 := (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (by simpa using hc4)).some
  let ep := MulEquiv.ofBijective (BenderSuzuki.Converse.pi (GaloisField 2 2))
    ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩
  let e := (a (if i then 1 else 0)).some.trans (e4.symm.trans ep.symm)
  let ey := (a (if !i then 1 else 0)).some.trans (e4.symm.trans ep.symm)
  have hlocal := source_linear_graphLocalGroup_eq_star h i e
  obtain ⟨T, hT⟩ := source_linear_initial_sylow h i (by decide : 0 < 2) hc4 e
  obtain ⟨Ty, hTy⟩ := source_linear_initial_sylow h (!i) (by decide : 0 < 2) hc4 ey
  have hTy' : (Ty : Subgroup (star L S (!i))).map (star L S (!i)).subtype = Q F m ⊔ Q F y := by
    simpa only [Bool.not_not] using hTy
  obtain ⟨R, hR⟩ := (a5_pair_reduced_edge_sylows h a hum.symm).2
  have hR' : ∃ R : Sylow 2 (star L S i),
      (R : Subgroup (star L S i)).map (star L S i).subtype = Q F u ⊔ Q F m := by
    rw [← hlocal]
    exact ⟨R, by simpa only [sup_comm] using hR⟩
  obtain ⟨R, hR⟩ := hR'
  obtain ⟨_, hz, _, hzy, hcommy⟩ := a5_pair_commuting_orbit_geometry h a hc hvu hd hcomm hmy htm
  obtain ⟨_, _, _, hzx, hcommx⟩ := a5_pair_commuting_orbit_geometry h a hc hvu hd hcomm hum.symm htm
  obtain ⟨hcard, hmin⟩ := a5_pair_commuting_center_card_and_minimal h a hc hvu hd hcomm hmy htm
  have hcardy := a5_pair_commuting_neighboring_center_card h a hc hvu hd hcomm hmy htm
  have hz' : center (star L S i) = ⊥ := by rw [←hlocal]; exact hz
  have hmin' : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z F m).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z F m).subgroupOf (star L S i) := by
    intro N hN hNZ
    let := hN
    have hnorm : star L S i ≤ normalizer (N.map (star L S i).subtype : Set (Reduction.G₀ L S)) := by
      have hh := N.le_normalizer_map (star L S i).subtype
      simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
    have hNZ' : N.map (star L S i).subtype ≤ Z F m := by
      rintro z ⟨n, hn, rfl⟩
      exact hNZ hn
    rcases hmin (N.map (star L S i).subtype) hNZ' (hlocal.symm ▸ hnorm) with hzero | heq
    · exact Or.inl ((map_eq_bot_iff_of_injective _ (star L S i).subtype_injective).mp hzero)
    · right
      have hh := congrArg (Subgroup.comap (star L S i).subtype) heq
      rwa [comap_map_eq_self_of_injective (star L S i).subtype_injective] at hh
  obtain ⟨σ, hcross, hsmall, hactor⟩ :=
    a5_pair_commuting_conjugated_intersection_indices h a hc hvu hd hcomm hum hmy.symm
  obtain ⟨hnatcard, _⟩ := source_linear_intersection_natural h i hb hum.symm hne T R hT hR e hz'
    (by simpa [hc4] using hcard) (by simpa [hc4] using hcardy) hzx hzy
    hcommx.le hcommy.le hcross (by simpa [hc4] using hsmall.le)
    (by simpa [hc4] using hactor) ey rfl Ty hTy' hc hvu.symm hmin'
  let D := V F y 1
  let := V_elementary F ht.generate (fun t => (source_Z_Q_U ht t).1)
    (Reduction.reduced_kernel_sylow h) hb y
  let : ((Z F y).subgroupOf D).Normal := normal_of_isMulCommutative _
  have hZcard : Nat.card ((Z F y).subgroupOf D) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe (Z_le_V F y 1)).toEquiv).trans hcardy
  have hD := card_eq_card_quotient_mul_card_subgroup ((Z F y).subgroupOf D)
  rw [hnatcard, hc4, hZcard] at hD
  exact hD


/-- Original A5/A5 source consequence with all auxiliary data constructed internally. -/
theorem a5_pair_not_commuting_based_three_path
    (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    (i : Bool) {v u : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) v (base (Reduction.reducedFamily L S) (!i)))
    (hvu : (graph (Reduction.reducedFamily L S)).Adj v u)
    (hd : (graph (Reduction.reducedFamily L S)).dist u (base (Reduction.reducedFamily L S) (!i)) + 1 =
      b (Reduction.reducedFamily L S))
    (hcomm : ⁅Z (Reduction.reducedFamily L S) v, Z (Reduction.reducedFamily L S) (base (Reduction.reducedFamily L S) (!i))⁆ = ⊥)
    (hum : (graph (Reduction.reducedFamily L S)).Adj u (base (Reduction.reducedFamily L S) i)) :
    False := by
  let F := Reduction.reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let ht := Reduction.reduced_triple h
  let : ∀ j, Finite (F j) := finite_endpoints ht
  have hmy : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨hb3, hne⟩ := a5_pair_commuting_critical_remaining h a hc hvu hd hcomm
  have hb : 2 < b F := by
    change 2 < b (Reduction.reducedFamily L S)
    omega
  have htm : v.type = m.type := (Bool.eq_not_of_ne hvu.1).trans
    (Bool.eq_not_of_ne hum.1.symm).symm
  have hcardZ := (a5_pair_commuting_center_card_and_minimal h a hc hvu hd hcomm hmy htm).1
  have hcardV := a5_pair_commuting_based_span_card h a i hc hvu hd hcomm hum
  have hZmVy : Z F m ≤ V F y 1 := Z_neighbor_le_V F hmy.symm
  have hZmVu : Z F m ≤ V F u 1 := Z_neighbor_le_V F hum
  let := V_elementary F ht.generate (fun t => (source_Z_Q_U ht t).1)
    (Reduction.reduced_kernel_sylow h) hb u
  have hcentral : Z F m ≤ centralizer (V F u 1 : Set (Reduction.G₀ L S)) := by
    intro z hz t ht'
    exact congrArg Subtype.val (mul_comm (⟨t, ht'⟩ : V F u 1) ⟨z, hZmVu hz⟩)
  have hindex : (Z F m).relIndex (V F y 1) = 4 := by
    have hh := ((Z F m).subgroupOf (V F y 1)).card_mul_index
    have hz : Nat.card ((Z F m).subgroupOf (V F y 1)) = 16 :=
      (Nat.card_congr (subgroupOfEquivOfLe hZmVy).toEquiv).trans hcardZ
    change Nat.card ((Z F m).subgroupOf (V F y 1)) * (Z F m).relIndex (V F y 1) =
      Nat.card (V F y 1) at hh
    rw [hz, hcardV] at hh
    omega
  have hbound : (centralizer (V F u 1 : Set (Reduction.G₀ L S))).relIndex (V F y 1) ≤ 4 := by
    have hh := relIndex_le_of_le_left hcentral (by rw [hindex]; decide)
    exact hh.trans_eq hindex
  have models (z : Vertex F) : IsRankOneModel (graphLocalGroup F z ⧸ pCore 2 (graphLocalGroup F z)) :=
    .linear 2 (by decide) (a5_pair_reduced_graph_linear_four h a z)
  obtain ⟨_, z, hzy, hcz, hdz, hcommz, _⟩ := reduced_reciprocal_critical_configuration h
    (Reduction.reduced_graph_core_obstruction h) models hc hvu hd (by omega) hcomm hne
  obtain ⟨_, hnez⟩ := a5_pair_commuting_critical_remaining h a hcz hzy hdz hcommz
  have hactor := a5_pair_commuting_span_core_index h a hcz hzy hdz hcommz
  obtain ⟨K, _, _, hK, ⟨eK⟩⟩ := a5_pair_reduced_graph_linear_four h a y
  let := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  let e := eK.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
    ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩).symm
  have hres := CommutingTrivial.reduced_critical_saturated_residual_natural h hcz hzy hdz
    (by omega) hcommz (Reduction.reduced_graph_core_obstruction h z y hzy)
    (by decide : 0 < 2) hK e (hactor.trans hK.symm) (hbound.trans_eq hK.symm)
  exact reduced_natural_residual_exclusion_of_catalogue h models hcz hzy hdz
    (by omega) hcommz hnez (by decide : 0 < 2) hK e hres


/-- Original A5/A5 source consequence with all auxiliary data constructed internally. -/
theorem a5_pair_critical_first_edge_not_commuting
    (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    {v u w : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) v w)
    (hvu : (graph (Reduction.reducedFamily L S)).Adj v u)
    (hd : (graph (Reduction.reducedFamily L S)).dist u w + 1 =
      b (Reduction.reducedFamily L S)) :
    ⁅Z (Reduction.reducedFamily L S) v, Z (Reduction.reducedFamily L S) w⁆ ≠ ⊥ := by
  intro hcomm
  let F := Reduction.reducedFamily L S
  let ht := Reduction.reduced_triple h
  let : ∀ j, Finite (F j) := finite_endpoints ht
  obtain ⟨hb3, _⟩ := a5_pair_commuting_critical_remaining h a hc hvu hd hcomm
  have huw : u ≠ w := by
    intro he
    rw [he, SimpleGraph.dist_self] at hd
    omega
  obtain ⟨m, hwm, hdm⟩ := exists_predecessor F ht.generate u w huw
  have hum : (graph F).Adj u m := SimpleGraph.dist_eq_one_iff_adj.mp (by
    change (graph F).dist u w + 1 = b F at hd
    change b F = 3 at hb3
    omega)
  obtain ⟨g, hgm, hgw⟩ := incident_common_translate F hwm.symm.2
  have htw : w.type = !m.type := Bool.eq_not_of_ne hwm.1
  rw [htw] at hgw
  have hbackm : g⁻¹ • m = base F m.type := by
    have hh := congrArg (fun z : Vertex F => g⁻¹ • z) hgm
    simpa only [inv_smul_smul] using hh.symm
  have hbackw : g⁻¹ • w = base F (!m.type) := by rw [←hgw, inv_smul_smul]
  have hc' := criticalPair_translate F hc g⁻¹
  rw [hbackw] at hc'
  have hvu' : (graph F).Adj (g⁻¹ • v) (g⁻¹ • u) :=
    (Subgroup.CosetGeometry.translationGraphIso F g⁻¹).map_adj_iff.mpr hvu
  have hd' : (graph F).dist (g⁻¹ • u) (base F (!m.type)) + 1 = b F := by
    rw [←hbackw, Subgroup.CosetGeometry.RankTwo.dist_smul]
    exact hd
  have hcomm' : ⁅Z F (g⁻¹ • v), Z F (base F (!m.type))⁆ = ⊥ := by
    rw [←hbackw, commuting_centers_translate, hcomm, Subgroup.map_bot]
  have hum' : (graph F).Adj (g⁻¹ • u) (base F m.type) := by
    rw [←hbackm]
    exact (Subgroup.CosetGeometry.translationGraphIso F g⁻¹).map_adj_iff.mpr hum
  exact a5_pair_not_commuting_based_three_path h a m.type hc' hvu' hd' hcomm' hum'


/-- Original A5/A5 source consequence with all auxiliary data constructed internally. -/
theorem a5_pair_critical_not_commuting
    (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    {v w : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) v w) :
    ⁅Z (Reduction.reducedFamily L S) v, Z (Reduction.reducedFamily L S) w⁆ ≠ ⊥ := by
  let F := Reduction.reducedFamily L S
  let ht := Reduction.reduced_triple h
  have hb := source_b_positive ht
  change 0 < b (Reduction.reducedFamily L S) at hb
  have hne : w ≠ v := by
    intro he
    have hh := hc.1
    rw [he, SimpleGraph.dist_self] at hh
    omega
  obtain ⟨u, hvu, hdu⟩ := exists_predecessor F ht.generate w v hne
  have hd : (graph F).dist u w + 1 = b F := by
    calc
      (graph F).dist u w + 1 = (graph F).dist w u + 1 := by rw [SimpleGraph.dist_comm]
      _ = (graph F).dist w v := hdu
      _ = (graph F).dist v w := SimpleGraph.dist_comm
      _ = b F := hc.1
  exact a5_pair_critical_first_edge_not_commuting h a hc hvu hd

end CFSG.Quasithin.ChapterF.Source
