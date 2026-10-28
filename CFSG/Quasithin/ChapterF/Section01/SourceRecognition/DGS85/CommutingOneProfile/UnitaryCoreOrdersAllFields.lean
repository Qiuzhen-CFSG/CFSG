module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryCoreUpperAllFields
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryCoreOrders
public import Theory.ElementaryAbelian.ExtraspecialOrder
/-!
# Exact unitary core orders in every field

The three-center normal-closure argument gives the core upper bound also
when the fixed field has order two. In that case the source special-core
equality has center of order two, and nonelementarity of S/Q_beta gives
|Q_beta|>32. The alternating commutator pairing of this extraspecial group
makes its order an odd power of two, so the upper bound 128 is exact.
For larger fields the existing faithful Frattini degree bound is reused.

The literal edge indices then give |Q_beta|=2^(7n), |S|=2^(10n),
|Q_alpha|=2^(8n) and |Q_alpha/Z_alpha|=2^(4n). Both unitary markings
are retained. ReducedUnitaryCoreOrdersAllFields applies the result under
the original inclusion and to O₂ of the full common Borel. Natural action
on the alpha section is a further source obligation, not a cardinality claim.
Source: DGS85, Groups and Graphs (1985), (5.7), (11.6), (11.8), pp.108,172--176.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem binary_core_order (R Z : Subgroup G) [Finite R]
    (hcenter : centerIn R = Z) (hZ : Nat.card Z = 2)
    (he : ∃ hN : (Z.subgroupOf R).Normal, letI := hN
      IsElementaryAbelian 2 (R ⧸ Z.subgroupOf R))
    (hl : 32 < Nat.card R) (hu : Nat.card R ≤ 128) : Nat.card R = 128 := by
  have hc : Nat.card (center R) = 2 := by
    rw [←card_map_of_injective (K := center R) R.subtype_injective,←centerIn_eq_map_center,hcenter,hZ]
  have hz : Z.subgroupOf R = center R := by
    apply map_injective R.subtype_injective
    rw [map_subgroupOf_eq_of_le (hcenter ▸ inf_le_left),←centerIn_eq_map_center,hcenter]
  obtain ⟨hN,hE⟩ := he
  let := hN
  have hEq : IsElementaryAbelian 2 (R ⧸ center R) := by
    let := hE
    let e := QuotientGroup.congr (Z.subgroupOf R) (center R) (MulEquiv.refl R)
      (by simpa using hz)
    exact IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
  let := hEq
  have hcount := (center R).card_mul_index
  rw [hc,index_eq_card] at hcount
  let : Nontrivial (R ⧸ center R) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsExtraspecial 2 R := ⟨hc,hEq,inferInstance⟩
  exact IsExtraspecial.card_eq_128_of_bounds hl hu

private theorem all_unitary_order_core_sup_index (A C : Subgroup G)
    (hn : C ≤ normalizer (A : Set G)) : A.relIndex (A ⊔ C) = A.relIndex C := by
  let H := A ⊔ C
  let : (A.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le A.le_normalizer hn)
  have he := relIndex_sup_left (C.subgroupOf H) (A.subgroupOf H)
  rw [←subgroupOf_sup le_sup_left le_sup_right,relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right] at he
  exact he

theorem source_nonElementary_unitary_core_orders_all_fields_on_escaping_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hesc : ¬ Z (family P) b ≤ Q (family P) (g • b))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices)
    (hne : ∃ hN : ((Q (family P) b).subgroupOf
        ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) ⧸
        (Q (family P) b).subgroupOf ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)))
    {n : ℕ} (hn : 0 < n)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n)) :
    (Z (family P) b).relIndex (Q (family P) b) = 2^(6*n) ∧
      Nat.card (Q (family P) b) = 2^(7*n) ∧
      Nat.card ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) = 2^(10*n) ∧
      Nat.card (Q (family P) a) = 2^(8*n) ∧
      (Z (family P) a).relIndex (Q (family P) a) = 2^(4*n) := by
  let := finite_endpoints h
  let qα := (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b)
  let qβ := (Q (family P) b).relIndex (Z (family P) a)
  have hab := source_critical_one_adjacent hc hb
  have hu := source_unitary_core_upper_all_fields_on_escaping_path h hB hS d hc hb hcomm hbc hac
    Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp hn mark
  have horders := source_center_seed_pair_orders_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
  have hZ := source_unitary_center_card_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp n (by omega) mark
  have hβ : qβ = 2^n := horders.1.symm.trans hZ
  have hfield := (source_field_parameters_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp).1
  change qα = qβ^2 at hfield
  have hα : qα = 2^(2*n) := by rw [hfield,hβ,←pow_mul]; congr 1; omega
  have hl : 2^(6*n) ≤ (Z (family P) b).relIndex (Q (family P) b) := by
    by_cases hn1 : n = 1
    · let R := Q (family P) b
      let : Finite R := Finite.of_injective (inclusion (Q_le_stabilizer _ b)) (inclusion_injective _)
      have hz2 : Nat.card (Z (family P) b) = 2 := by simpa only [hn1,pow_one] using hZ
      have hlower := (source_nonElementary_beta_core_lower_bound_on_escaping_path h hB hS d
        hc hb hcomm hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp hne).1
      change qα^2*qβ < Nat.card R at hlower
      rw [hα,hβ,hn1] at hlower
      norm_num at hlower
      have hupper := hu.2.2.1
      rw [hn1] at hupper
      norm_num at hupper
      have hs := source_beta_core_special_on_escaping_path h hB hS d hc hb hcomm hbc hac
        Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
      have he := (source_beta_core_layers_on_escaping_path h hB hS d hc hb hcomm hbc hac
        Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp).2.2.2.2.2
      have hr : Nat.card R = 128 := binary_core_order R (Z (family P) b) hs.1 hz2 he hlower hupper
      have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (Z (family P) b) R bot_le
        ((source_Z_Q_U h b).1.trans (map_subtype_le _))
      simp only [relIndex_bot_left,hz2,hr] at hh
      change 2^(6*n) ≤ (Z (family P) b).relIndex R
      rw [hn1]
      norm_num
      omega
    · exact source_unitary_core_lower_on_escaping_path h hB hS d hc hb hcomm hbc hac
        Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp (by omega) mark
  have hix : (Z (family P) b).relIndex (Q (family P) b) = 2^(6*n) := by
    apply le_antisymm _ hl
    calc
      (Z (family P) b).relIndex (Q (family P) b) ≤ qα^3 := hu.1
      _ = 2^(6*n) := by rw [hα,←pow_mul]; congr 1; omega
  have hZQ : Z (family P) b ≤ Q (family P) b :=
    (source_Z_Q_U h b).1.trans (map_subtype_le _)
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup G) (Z (family P) b)
    (Q (family P) b) bot_le hZQ
  simp only [relIndex_bot_left,hZ,hix] at hcount
  have hQb : Nat.card (Q (family P) b) = 2^(7*n) := by
    rw [←hcount,←pow_add]; congr 1; omega
  have hQbS : Q (family P) b ≤ (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 := by
    simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab.symm
  have hScount := relIndex_mul_relIndex (⊥ : Subgroup G) (Q (family P) b)
    ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) bot_le hQbS
  simp only [relIndex_bot_left,hQb,source_unitary_edge_index h hB d hab (by omega) mark] at hScount
  have hSorder : Nat.card ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) =
      2^(10*n) := by
    rw [←hScount,←pow_mul,←pow_add]; congr 1; omega
  have hprod := (source_core_product_and_alpha_on_path h hB d hc hb hcomm hbc hac
    Ma Mb ht p hp ha hbp hcp).1
  have hcore := source_rankOne_pair_core_span_on_path h hB d hc hb hbc hac Ma Mb ht p hp ha hbp hcp
  have hsupp := alpha_supplement_of_pair_generation _ _ _ _ _ hprod hcore
    ((source_Z_Q_U h a).1.trans (map_subtype_le _))
  have hiα : (Q (family P) a).relIndex
      ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) = 2^(2*n) := by
    rw [hsupp,all_unitary_order_core_sup_index _ _
      (inf_le_right.trans (source_adjacent_core_normalizes_core h hab.symm))]
    exact hα
  have hQaCount := relIndex_mul_relIndex (⊥ : Subgroup G) (Q (family P) a)
    ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) bot_le
      (Noncommuting.graph_Q_le_edgeCore h hab)
  simp only [relIndex_bot_left,hiα,hSorder] at hQaCount
  have hQa : Nat.card (Q (family P) a) = 2^(8*n) := by
    apply Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2^(2*n))
    calc
      Nat.card (Q (family P) a) * 2^(2*n) = 2^(10*n) := hQaCount
      _ = 2^(8*n) * 2^(2*n) := by rw [←pow_add]; congr 1; omega
  have hZa : Nat.card (Z (family P) a) = 2^(4*n) := by
    calc
      Nat.card (Z (family P) a) = qα*qβ^2 := horders.2.2.1
      _ = 2^(4*n) := by rw [hα,hβ,←pow_mul,←pow_add]; congr 1; omega
  refine ⟨hix,hQb,hSorder,hQa,?_⟩
  have hZaCount := relIndex_mul_relIndex (⊥ : Subgroup G) (Z (family P) a)
    (Q (family P) a) bot_le ((source_Z_Q_U h a).1.trans (map_subtype_le _))
  simp only [relIndex_bot_left,hZa,hQa] at hZaCount
  apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2^(4*n))
  calc
    2^(4*n) * (Z (family P) a).relIndex (Q (family P) a) = 2^(8*n) := hZaCount
    _ = 2^(4*n) * 2^(4*n) := by rw [←pow_add]; congr 1; omega

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
