module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryCoreUpper
public import Theory.SpecificGroups.SU3.ThreeOmegaNormalClosure
/-!
# Whole unitary core upper bounds, including the binary parameter

Three conjugate omega-centers generate their normal closure in both unitary
coverings. Lifting through the actual local quotient bounds every neighboring
center by the three chosen centers and Q_beta. Their three-core intersection
is therefore normalized by the full neighboring-center span. Source (6.2)(b)
makes that span transitive, identifying the intersection with I_beta=Z_beta.
The three indices give |Q_beta| ≤ 2^(7n) and |S| ≤ 2^(10n).

The proof uses only positive field degree; at degree one it does not assert
that three centers generate SU₃(2). The literal source quotient, full graph
kernel and core remain distinct. UnitaryCoreOrdersAllFields combines the
bound with the special-core calculation in the nonelementary branch.
Source: DGS85, Groups and Graphs (1985), (5.4), (6.2)(b), (11.6), (11.8),
pp.106,119,172--176.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open BenderSuzuki.MatrixGroups Representation.SU3.CubicDegree.InnerActors
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
private theorem unitary_omega_normal_closure {K : Type*} [Group K] [Finite K]
    {n : ℕ} (hn : 0 < n) (mark : ClassicalGroup.IsPSU K 3 (2^n) ∨ IsSU K 3 (2^n))
    (T : Sylow 2 K) : ∃ c : Fin 3 → K, ∀ g : K,
      (omegaCenterIn (T : Subgroup K)).map (MulAut.conj g).toMonoidHom ≤
      (⨆ i, (omegaCenterIn (T : Subgroup K)).map (MulAut.conj (c i)).toMonoidHom) := by
  rcases mark with mark | mark
  · obtain ⟨E,_,_,J,hcard,hconj,⟨e⟩⟩ := mark
    exact HermitianForm.ThreeOmegaNormalClosure.of_equiv e
      (HermitianForm.ThreeOmegaNormalClosure.projective J hn hcard hconj) T
  · obtain ⟨E,_,_,J,hcard,hconj,⟨e⟩⟩ := mark
    exact HermitianForm.ThreeOmegaNormalClosure.of_equiv e
      (HermitianForm.ThreeOmegaNormalClosure.special J hn hcard hconj) T

theorem source_unitary_three_center_span
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    {n : ℕ} (hn : 0 < n)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n)) :
    ∃ t : Fin 3 → d.localGroup b,
      ∀ u : d.localGroup b, Z (family P) ((u : G) • a) ≤
        (⨆ i, Z (family P) ((t i : G) • a)) ⊔ Q (family P) b := by
  let := finite_endpoints h
  let L := d.localGroup b
  let : Finite L := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  let : Finite (L ⧸ pCore 2 L) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  let q := QuotientGroup.mk' (pCore 2 L)
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d (source_critical_one_adjacent hc hb).symm
  have hZA : Z (family P) a ≤ L := ((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
    ((show Q (family P) a ≤ (stabilizer (family P) b ⊓ stabilizer (family P) a).pCoreIn 2 from
      by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h (source_critical_one_adjacent hc hb)).trans
        (hT ▸ map_subtype_le _))
  have him := source_rankOne_center_image_omega h hB d hc hb Mb T hT
  obtain ⟨c,hc'⟩ := unitary_omega_normal_closure hn mark (T.mapSurjective (QuotientGroup.mk'_surjective _))
  choose t ht using fun i => QuotientGroup.mk'_surjective (pCore 2 L) (c i)
  change ∀ i, q (t i) = c i at ht
  change ((Z (family P) a).subgroupOf L).map q = _ at him
  let W : Subgroup L := ⨆ i, ((Z (family P) a).subgroupOf L).map (MulAut.conj (t i)).toMonoidHom
  refine ⟨t,?_⟩
  intro u
  have hW : (((Z (family P) a).subgroupOf L).map
      (MulAut.conj u).toMonoidHom).map q ≤ W.map q := by
    rw [Subgroup.map_iSup]
    simpa only [ThreeRoots.map_conjugate,him,ht,Sylow.coe_mapSurjective] using hc' (q u)
  have hle : ((Z (family P) a).subgroupOf L).map (MulAut.conj u).toMonoidHom ≤
      W ⊔ pCore 2 L := by
    have hh := (le_comap_map q _ : ((Z (family P) a).subgroupOf L).map
      (MulAut.conj u).toMonoidHom ≤
      ((((Z (family P) a).subgroupOf L).map (MulAut.conj u).toMonoidHom).map q).comap q)
    have hhh := hh.trans (comap_mono hW)
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk'] using hhh
  have hm := map_mono (f := L.subtype) hle
  rw [Subgroup.map_sup,Subgroup.map_iSup,
    show (pCore 2 L).map L.subtype = Q (family P) b from localGroup_core_eq (family P) d b] at hm
  simpa only [ThreeRoots.map_conjugate,map_subgroupOf_eq_of_le hZA,←Z_translate,
    Subgroup.subtype_apply,L] using hm

theorem source_unitary_three_core_intersection_all_fields
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    {n : ℕ} (hn : 0 < n)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n)) :
    ∃ t : Fin 3 → d.localGroup b,
      (⨅ i, Q (family P) ((t i : G) • a)) = neighborCoreIntersection (family P) b := by
  let := finite_endpoints h
  obtain ⟨t,ht⟩ := source_unitary_three_center_span h hB d hc hb Mb hn mark
  let K : Subgroup G := ⨅ i, Q (family P) ((t i : G) • a)
  have hadj (i : Fin 3) : (graph (family P)).Adj b ((t i : G) • a) := by
    have he : (t i : G) • b = b := d.local_le b (t i).property
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) (t i : G)).map_adj_iff.mpr (source_critical_one_adjacent hc hb).symm
    change (graph (family P)).Adj ((t i : G) • b) ((t i : G) • a) at hh
    rwa [he] at hh
  have hQn : Q (family P) b ≤ normalizer (K : Set G) := by
    apply le_normalizer_iff.mpr
    intro x hx y hy
    apply mem_iInf.mpr
    intro i
    exact le_normalizer_iff.mp (stabilizer_normalizes_Q (family P) ((t i : G) • a)) x
      (((source_Z_Q_U h b).2.trans ((ballKernel_one_le_edge _ (hadj i)).trans inf_le_right)) hx)
      y (mem_iInf.mp hy i)
  have hZn : (⨆ i, Z (family P) ((t i : G) • a)) ≤ normalizer (K : Set G) := by
    apply iSup_le
    intro i
    exact ((le_centralizer_iff.mp (source_core_centralizes_center h _)).trans
      (centralizer_le (show K ≤ Q (family P) ((t i : G) • a) from iInf_le _ i))).trans
        (Subgroup.centralizer_le_normalizer (K : Set G))
  let R := conjugateSpanBy (Z (family P) a) (stabilizer (family P) b)
  have hRn : R ≤ normalizer (K : Set G) := by
    apply (closure_le _).mpr
    rintro z ⟨u,hu,x,hx,rfl⟩
    have hbu : (graph (family P)).Adj b (u • a) := by
      have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) u).map_adj_iff.mpr
        (source_critical_one_adjacent hc hb).symm
      change (graph (family P)).Adj (u • b) (u • a) at hh
      rwa [show u • b = b from hu] at hh
    obtain ⟨v,hv,hva⟩ := d.transitive b
      ⟨a,(source_critical_one_adjacent hc hb).symm⟩ ⟨u • a,hbu⟩
    have hZ := (ht (⟨v,hv⟩ : d.localGroup b)).trans (sup_le hZn hQn)
    change Z (family P) (v • a) ≤ normalizer (K : Set G) at hZ
    rw [hva,Z_translate] at hZ
    exact hZ (mem_map_of_mem (MulAut.conj u).toMonoidHom hx)
  have hZa : Z (family P) a ≤ stabilizer (family P) b :=
    ((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
      ((source_Z_Q_U h a).2.trans ((ballKernel_one_le_edge _
        (source_critical_one_adjacent hc hb)).trans inf_le_right))
  have htrans (w : (graph (family P)).neighborSet b) :
      ∃ u ∈ R, u • ((t 0 : G) • a) = w := by
    obtain ⟨v,hv,hv0⟩ := source_nonclosed_normal_transitive h hB
      (source_critical_one_adjacent hc hb).symm R (conjugateSpanBy_le_self hZa)
      (le_normalizer_conjugateSpanBy _ _)
      (source_critical_center_span_not_twoClosed h hc hb) _ (hadj 0)
    obtain ⟨u,hu,hu0⟩ := source_nonclosed_normal_transitive h hB
      (source_critical_one_adjacent hc hb).symm R (conjugateSpanBy_le_self hZa)
      (le_normalizer_conjugateSpanBy _ _)
      (source_critical_center_span_not_twoClosed h hc hb) w w.property
    exact ⟨u*v⁻¹,R.mul_mem hu (R.inv_mem hv),by rw [mul_smul,←hv0,inv_smul_smul,hu0]⟩
  refine ⟨t,le_antisymm ?_ ?_⟩
  · intro x hx
    apply mem_iInf.mpr
    intro w
    obtain ⟨u,hu,hua⟩ := htrans w
    have hmap : K.map (MulAut.conj u).toMonoidHom = K := mem_normalizer_iff_map_conj_eq.mp (hRn hu)
    have hh := map_mono (f := (MulAut.conj u).toMonoidHom) (iInf_le (fun i => Q (family P) ((t i : G) • a)) 0)
    rw [hmap,←Q_translate,hua] at hh
    exact hh hx
  · apply le_iInf
    intro i
    exact neighborCoreIntersection_le _ (hadj i).symm

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
discharged at the actual escaping source path. -/
theorem source_unitary_core_upper_all_fields_on_escaping_path
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
    {n : ℕ} (hn : 0 < n)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n)) :
    let qα := (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b)
    let qβ := (Q (family P) b).relIndex (Z (family P) a)
    (Z (family P) b).relIndex (Q (family P) b) ≤ qα^3 ∧
      Nat.card (Q (family P) b) ≤ qα^3 * qβ ∧
      Nat.card (Q (family P) b) ≤ 2^(7*n) ∧
      Nat.card ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) ≤ 2^(10*n) := by
  let := finite_endpoints h
  let qα := (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b)
  let qβ := (Q (family P) b).relIndex (Z (family P) a)
  have hab := source_critical_one_adjacent hc hb
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
  have hIc := source_neighbor_intersection_eq_center_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
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
  have hZ := (source_center_seed_pair_orders_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp).1
  change Nat.card (Z (family P) b) = qβ at hZ
  have hcub : Nat.card (Q (family P) b) ≤ qα^3*qβ := by
    rw [←hcard,hZ,Nat.mul_comm]
    exact Nat.mul_le_mul_right qβ hbound
  have hfield := (source_field_parameters_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp).1
  change qα = qβ^2 at hfield
  have hunit := source_unitary_center_card_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp n (by omega) mark
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

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
