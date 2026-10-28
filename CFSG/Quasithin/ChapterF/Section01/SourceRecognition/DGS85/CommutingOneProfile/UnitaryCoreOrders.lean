module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryCoreUpper
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.BetaCoreSpecial
public import Theory.Representation.SU3.CharacteristicTwoFrattini
public import Theory.Frattini.OmegaProducts

/-!
# Exact nonbinary unitary core orders

The actual beta local group has self-centralizing two-core. Its quotient
therefore acts faithfully on the Frattini quotient of that core. The proved
special-group equality identifies the Frattini subgroup with Z_beta; the
unitary degree bound then gives index at least 2^(6m). Three neighboring
cores give the reverse bound. This proves the exact beta-core order
2^(7m) and edge two-core order 2^(10m).

The literal alpha edge index and the already identified alpha-center order
then give |Q_alpha| = 2^(8m) and |Q_alpha/Z_alpha| = 2^(4m). The result keeps
both unitary quotient markings and assumes m ≥ 2, as required by the degree
and three-center arguments. The binary case and natural action on the
alpha section require their separate source proofs. ReducedUnitaryCoreOrders
transports all five identities to the original completion and full Borel.
Source: DGS85, Groups and Graphs (1985), (5.7), p.108, and (11.8), pp.175--176.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
/-- The actual beta Frattini action gives the matching lower index bound. -/
theorem source_unitary_core_lower_on_escaping_path
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
  have hphi := (source_beta_core_special_on_escaping_path h hB hS d hc hb hcomm hbc hac
    Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp).2.2.1
  have hind : (Z (family P) b).relIndex R = Nat.card (R ⧸ frattini R) := by
    rw [←hphi]
    have hh := relIndex_map_map_of_injective (frattini R) (⊤ : Subgroup R) R.subtype_injective
    rw [←MonoidHom.range_eq_map,range_subtype,relIndex_top_right,index_eq_card] at hh
    exact hh
  rwa [hind]

private theorem order_core_sup_index (A C : Subgroup G)
    (hn : C ≤ normalizer (A : Set G)) : A.relIndex (A ⊔ C) = A.relIndex C := by
  let H := A ⊔ C
  let : (A.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le A.le_normalizer hn)
  have he := relIndex_sup_left (C.subgroupOf H) (A.subgroupOf H)
  rw [←subgroupOf_sup le_sup_left le_sup_right,relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right] at he
  exact he

/-- Exact source core and central-section orders for both nonbinary unitary covers. -/
theorem source_unitary_core_orders_on_escaping_path
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
    {n : ℕ} (hn : 2 ≤ n)
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
  have hl := source_unitary_core_lower_on_escaping_path h hB hS d hc hb hcomm hbc hac
    Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp hn mark
  have hu := source_unitary_core_upper_on_escaping_path h hB hS d hc hb hcomm hbc hac
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
    rw [hsupp,order_core_sup_index _ _
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
