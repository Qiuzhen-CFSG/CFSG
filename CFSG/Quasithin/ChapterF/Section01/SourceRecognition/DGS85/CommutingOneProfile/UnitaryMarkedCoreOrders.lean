module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryBetaSpecial
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryCoreOrdersAllFields
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryBorel

/-!
# Exact unitary core orders from the marked source hypotheses

Three neighboring alpha cores bound |Q_beta:Z_beta| above by q_alpha cubed.
The faithful unitary action on the special core's Frattini quotient supplies
the matching lower bound in larger fields. In degree one, nonelementarity
and the extraspecial odd-exponent order formula force the same equality.
The edge indices and center orders then give |Q_beta|=2^(7n), |S|=2^(10n),
|Q_alpha|=2^(8n), and |Q_alpha:Z_alpha|=2^(4n).

Every use of a path supplement is on the constructed two-edge path. The
unitary marking supplies nonelementarity, the special core, and the field
relation without assuming longer-walk transitivity. OriginalUnitaryCoreOrders
transports these orders to the literal full original Borel.
Source: DGS85, Groups and Graphs, (5.7), (11.6), (11.8), pp.108,172--176.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem all_field_core_sup_index (A C : Subgroup G)
    (hn : C ≤ normalizer (A : Set G)) : A.relIndex (A ⊔ C) = A.relIndex C := by
  let H := A ⊔ C
  let : (A.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le A.le_normalizer hn)
  have he := relIndex_sup_left (C.subgroupOf H) (A.subgroupOf H)
  rw [←subgroupOf_sup le_sup_left le_sup_right,relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right] at he
  exact he

open SimpleGraph SimpleGraph.PathTransitivePolygon
/-- The source whole-core upper bound for both unitary covers of every positive
fixed-field degree. The three-core intersection and all three indices are
discharged by the marked short-path calculation. -/
theorem source_unitary_core_upper_from_marking
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    {n : ℕ} (hn : 0 < n)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n)) :
    let qα := (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b)
    let qβ := (Q (family P) b).relIndex (Z (family P) a)
    (Z (family P) b).relIndex (Q (family P) b) ≤ qα^3 ∧
      Nat.card (Q (family P) b) ≤ qα^3 * qβ ∧
      Nat.card (Q (family P) b) ≤ 2^(7*n) ∧
      Nat.card ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) ≤ 2^(10*n) := by
  have hab := source_critical_one_adjacent hc hb
  let p : BasedWalk (graph (family P)) 2 a := ⟨⟨b,hab⟩,⟨⟨c,hbc⟩,PUnit.unit⟩⟩
  have hp : p.Nonbacktracking := ⟨hac.symm,trivial⟩
  have ht := source_unitary_beta_two_walk_transitive h hB d hab hn mark
  have ha : a ∈ p.vertices := by change a ∈ [a,b,c]; simp
  have hbp : b ∈ p.vertices := by change b ∈ [a,b,c]; simp
  have hcp : c ∈ p.vertices := by change c ∈ [a,b,c]; simp
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) :=
    mark.elim (IsRankOneModel.projective_unitary n hn) (IsRankOneModel.special_unitary n hn)

  let := finite_endpoints h
  let qα := (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b)
  let qβ := (Q (family P) b).relIndex (Z (family P) a)
  have hprod := (source_core_product_and_alpha_on_path h hB d hc hb hcomm hbc hac
    Ma Mb ht p hp ha hbp hcp).1
  have hcore := source_rankOne_pair_core_span_on_path h hB d hc hb hbc hac Ma Mb ht p hp ha hbp hcp
  have hsupp := alpha_supplement_of_pair_generation _ _ _ _ _ hprod hcore
    ((source_Z_Q_U h a).1.trans (map_subtype_le _))
  have hi : (Q (family P) a).relIndex (Q (family P) b) = qα := by
    rw [←all_field_core_sup_index _ _ (source_adjacent_core_normalizes_core h hab.symm),
      ←hprod,hsupp,all_field_core_sup_index _ _
        (inf_le_right.trans (source_adjacent_core_normalizes_core h hab.symm))]
  obtain ⟨t,htc⟩ := source_unitary_three_core_intersection_all_fields h hB d hc hb Mb hn mark
  have hIc := (source_unitary_neighbor_core_center_from_marking h hB hS d hc hb hcomm Ma hn mark).1
  have hit (i : Fin 3) : (Q (family P) ((t i : G) • a)).relIndex (Q (family P) b) = qα := by
    have he : (t i : G) • b = b := d.local_le b (t i).property
    have hQb : (Q (family P) b).map (MulAut.conj (t i : G)).toMonoidHom = Q (family P) b := by
      rw [←Q_translate,he]
    rw [Q_translate,←hQb,relIndex_map_map_of_injective _ _ (MulAut.conj (t i : G)).injective,hi]
  have hbound := relIndex_iInf_le (L := Q (family P) b) (fun i => Q (family P) ((t i : G) • a))
  rw [htc,hIc] at hbound
  simp only [hit,Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hbound
  have hZQ : Z (family P) b ≤ Q (family P) b := (source_Z_Q_U h b).1.trans (map_subtype_le _)
  have hcard := relIndex_mul_relIndex (⊥ : Subgroup G) (Z (family P) b) (Q (family P) b) bot_le hZQ
  simp only [relIndex_bot_left] at hcard
  have hZ := (source_unitary_center_seed_pair_orders h hB hS d hc hb hcomm hbc hac Ma hn mark).1
  change Nat.card (Z (family P) b) = qβ at hZ
  have hcub : Nat.card (Q (family P) b) ≤ qα^3*qβ := by
    rw [←hcard,hZ,Nat.mul_comm]
    exact Nat.mul_le_mul_right qβ hbound
  have hfield := (source_unitary_field_parameters_from_marking h hB hS d hc hb hcomm hbc hac Ma hn mark).1
  change qα = qβ^2 at hfield
  have hunit := source_unitary_center_card_from_marking h hB hS d hc hb hcomm hbc hac Ma hn mark
  have hβ : qβ = 2^n := hZ.symm.trans hunit
  have hseven : Nat.card (Q (family P) b) ≤ 2^(7*n) := by
    calc
      Nat.card (Q (family P) b) ≤ qα^3*qβ := hcub
      _ = 2^(7*n) := by rw [hfield,hβ,←pow_mul,←pow_mul,←pow_add]; congr 1; omega
  refine ⟨hbound,hcub,hseven,?_⟩
  have hQbS : Q (family P) b ≤ (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 := by
    simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab.symm
  have hS := relIndex_mul_relIndex (⊥ : Subgroup G) (Q (family P) b)
    ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) bot_le hQbS
  simp only [relIndex_bot_left,source_unitary_edge_index h hB d hab (by omega) mark] at hS
  calc
    Nat.card ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) =
        Nat.card (Q (family P) b) * (2^n)^3 := hS.symm
    _ ≤ 2^(7*n) * (2^n)^3 := Nat.mul_le_mul_right _ hseven
    _ = 2^(10*n) := by rw [←pow_mul,←pow_add]; congr 1; omega

/-- The actual beta Frattini action gives the matching lower index bound. -/
theorem source_unitary_core_lower_from_marking
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    {n : ℕ} (hn : 2 ≤ n)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n)) :
    2^(6*n) ≤ (Z (family P) b).relIndex (Q (family P) b) := by
  let := finite_endpoints h
  let L := d.localGroup b
  let R := Q (family P) b
  let : Finite L := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  let : (L.subgroupOf (stabilizer (family P) b)).Normal :=
    (normal_subgroupOf_iff_le_normalizer (d.local_le b)).mpr
      (localGroup_normalized (family P) d b)
  have hself : centralizer (pCore 2 L : Set L) ≤ pCore 2 L :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe (d.local_le b))).mp
      (normal_core_selfCentralizing (source_vertex_core_selfCentralizing h b)
        (L.subgroupOf (stabilizer (family P) b)))
  have hl : 2^(6*n) ≤ Nat.card (pCore 2 L ⧸ frattini (pCore 2 L)) := by
    rcases mark with mark | mark
    · obtain ⟨E,_,_,J,hcard,hconj,⟨e⟩⟩ := mark
      exact Representation.SU3.characteristic_two_frattini_card_lower hself J hn
        hcard hconj (Or.inr ⟨e⟩)
    · obtain ⟨E,_,_,J,hcard,hconj,⟨e⟩⟩ := mark
      exact Representation.SU3.characteristic_two_frattini_card_lower hself J hn
        hcard hconj (Or.inl ⟨e⟩)
  let eR : pCore 2 L ≃* R :=
    ((pCore 2 L).equivMapOfInjective L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr (localGroup_core_eq (family P) d b))
  have hcard := Nat.card_congr (QuotientGroup.congr _ _ eR (frattini_map_equiv eR)).toEquiv
  rw [hcard] at hl
  have hphi := (source_unitary_beta_core_special h hB hS d hc hb hcomm hbc hac Ma (by omega) mark).2.2.1
  have hind : (Z (family P) b).relIndex R = Nat.card (R ⧸ frattini R) := by
    rw [←hphi]
    have hh := relIndex_map_map_of_injective (frattini R) (⊤ : Subgroup R) R.subtype_injective
    rw [←MonoidHom.range_eq_map,range_subtype,relIndex_top_right,index_eq_card] at hh
    exact hh
  rwa [hind]

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

/-- The exact two-core orders and central indices for every positive marked
unitary degree, with no path-transitivity or nonelementarity input. -/
theorem source_unitary_core_orders_from_marking
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    {n : ℕ} (hn : 0 < n)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n)) :
    (Z (family P) b).relIndex (Q (family P) b) = 2^(6*n) ∧
      Nat.card (Q (family P) b) = 2^(7*n) ∧
      Nat.card ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) = 2^(10*n) ∧
      Nat.card (Q (family P) a) = 2^(8*n) ∧
      (Z (family P) a).relIndex (Q (family P) a) = 2^(4*n) := by
  have hab := source_critical_one_adjacent hc hb
  let p : BasedWalk (graph (family P)) 2 a := ⟨⟨b,hab⟩,⟨⟨c,hbc⟩,PUnit.unit⟩⟩
  have hp : p.Nonbacktracking := ⟨hac.symm,trivial⟩
  have ht := source_unitary_beta_two_walk_transitive h hB d hab hn mark
  have ha : a ∈ p.vertices := by change a ∈ [a,b,c]; simp
  have hbp : b ∈ p.vertices := by change b ∈ [a,b,c]; simp
  have hcp : c ∈ p.vertices := by change c ∈ [a,b,c]; simp
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) :=
    mark.elim (IsRankOneModel.projective_unitary n hn) (IsRankOneModel.special_unitary n hn)

  have hne : ∃ hN : ((Q (family P) b).subgroupOf
        ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)).Normal,
      letI := hN
      ¬ IsElementaryAbelian 2 (((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) ⧸
        (Q (family P) b).subgroupOf ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2)) := by
    have hh := source_unitary_edge_quotient_not_elementary h hB d hab.symm hn mark
    rw [inf_comm (stabilizer (family P) b) (stabilizer (family P) a)] at hh
    exact hh
  let := finite_endpoints h
  let qα := (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b)
  let qβ := (Q (family P) b).relIndex (Z (family P) a)
  have hu := source_unitary_core_upper_from_marking h hB hS d hc hb hcomm hbc hac Ma hn mark
  have horders := source_unitary_center_seed_pair_orders h hB hS d hc hb hcomm hbc hac Ma hn mark
  have hZ := source_unitary_center_card_from_marking h hB hS d hc hb hcomm hbc hac Ma hn mark
  have hβ : qβ = 2^n := horders.1.symm.trans hZ
  have hfield := (source_unitary_field_parameters_from_marking h hB hS d hc hb hcomm hbc hac Ma hn mark).1
  change qα = qβ^2 at hfield
  have hα : qα = 2^(2*n) := by rw [hfield,hβ,←pow_mul]; congr 1; omega
  have hl : 2^(6*n) ≤ (Z (family P) b).relIndex (Q (family P) b) := by
    by_cases hn1 : n = 1
    · let R := Q (family P) b
      let : Finite R := Finite.of_injective (inclusion (Q_le_stabilizer _ b)) (inclusion_injective _)
      have hz2 : Nat.card (Z (family P) b) = 2 := by simpa only [hn1,pow_one] using hZ
      have hlower := (source_unitary_beta_core_strict_lower h hB hS d hc hb hcomm hbc hac Ma hn mark hne).1
      change qα^2*qβ < Nat.card R at hlower
      rw [hα,hβ,hn1] at hlower
      norm_num at hlower
      have hupper := hu.2.2.1
      rw [hn1] at hupper
      norm_num at hupper
      have hs := source_unitary_beta_core_special h hB hS d hc hb hcomm hbc hac Ma hn mark
      have he := (source_unitary_beta_core_layers h hB hS d hc hb hcomm hbc hac Ma hn mark).2.2.2.2.2
      have hr : Nat.card R = 128 := binary_core_order R (Z (family P) b) hs.1 hz2 he hlower hupper
      have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (Z (family P) b) R bot_le
        ((source_Z_Q_U h b).1.trans (map_subtype_le _))
      simp only [relIndex_bot_left,hz2,hr] at hh
      change 2^(6*n) ≤ (Z (family P) b).relIndex R
      rw [hn1]
      norm_num
      omega
    · exact source_unitary_core_lower_from_marking h hB hS d hc hb hcomm hbc hac Ma (by omega) mark
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
