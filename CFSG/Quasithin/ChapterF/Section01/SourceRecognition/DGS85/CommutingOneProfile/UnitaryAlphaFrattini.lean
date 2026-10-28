module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryAlphaLayers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.AlphaFrattini

/-!
# The alpha Frattini subgroup from the unitary marking

The unitary Sylow Frattini bound puts Phi(Q_alpha) in Z_alpha Q_beta.
Irreducibility of Z_alpha and the trivial neighboring-core intersection
force Z_alpha into Phi(Q_alpha). The faithful alpha Frattini degree bound
and the exact core order make this inclusion an equality. Thus the literal
Q_alpha/Z_alpha is elementary abelian.

The marking constructs nonelementarity, and every required supplement
uses the two-edge path. UnitaryMarkedNatural applies the resulting quotient
to the actual conjugation action. Both unitary covers and degree one remain.
Source: DGS85, Groups and Graphs, (5.7), (11.5)--(11.8), pp.108,172--176.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem frattini_upper_transport {H K : Type*} [Group H] [Group K] [Finite H] [Finite K]
    (e : H ≃* K) (T : Sylow 2 H)
    (h : (frattini (T.mapSurjective (f := e.toMonoidHom) e.surjective)).map
      (T.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup K).subtype ≤
        omegaCenterIn (T.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup K)) :
    (frattini T).map (T : Subgroup H).subtype ≤ omegaCenterIn (T : Subgroup H) := by
  let U := (T : Subgroup H).map e.toMonoidHom
  change (frattini U).map U.subtype ≤ omegaCenterIn U at h
  let E := (T : Subgroup H).equivMapOfInjective e.toMonoidHom e.injective
  rintro x ⟨y,hy,rfl⟩
  have hyE : E y ∈ frattini U := by
    rw [←frattini_map_equiv E]
    exact mem_map_of_mem E.toMonoidHom hy
  have hh := h (mem_map_of_mem U.subtype hyE)
  change e (y : H) ∈ omegaCenterIn U at hh
  have hp := (mem_omegaCenterIn_iff _ _).mp hh
  apply (mem_omegaCenterIn_iff _ _).mpr
  refine ⟨y.property,?_,?_⟩
  · intro z hz
    apply e.injective
    simpa only [map_mul,Subgroup.subtype_apply] using hp.2.1 (e z) (mem_map_of_mem e.toMonoidHom hz)
  · apply e.injective
    simpa only [map_pow,map_one,Subgroup.subtype_apply] using hp.2.2

private theorem marked_unitary_frattini_upper
    {H : Type*} [Group H] [Finite H] {n : ℕ} (hn : 0 < n)
    (mark : ClassicalGroup.IsPSU H 3 (2^n) ∨ IsSU H 3 (2^n)) (T : Sylow 2 H) :
    (frattini T).map (T : Subgroup H).subtype ≤ omegaCenterIn (T : Subgroup H) := by
  rcases mark with ⟨E,_,_,J,hcard,hconj,⟨e⟩⟩ | ⟨E,_,_,J,hcard,hconj,⟨e⟩⟩
  · exact frattini_upper_transport e T
      (BenderSuzuki.MatrixGroups.HermitianForm.SylowFrattiniUpper.projective J hn hcard hconj _)
  · exact frattini_upper_transport e T
      (BenderSuzuki.MatrixGroups.HermitianForm.SylowFrattiniUpper.special J hn hcard hconj _)

private theorem alpha_frattini_le_center_join_beta
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    {n : ℕ} (hn : 0 < n)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n)) :
    (frattini (Q (family P) a)).map (Q (family P) a).subtype ≤
      Z (family P) a ⊔ Q (family P) b := by
  let := finite_endpoints h
  let L := d.localGroup b
  let R := Q (family P) a
  let : Finite L := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  let : Finite R := Finite.of_injective (inclusion (Q_le_stabilizer _ a)) (inclusion_injective _)
  let : Fact (IsPGroup 2 R) := ⟨isPGroup_pCoreIn 2 _⟩
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hab.symm
  have hRS : R ≤ (T : Subgroup L).map L.subtype := by
    rw [hT,inf_comm]
    exact Noncommuting.graph_Q_le_edgeCore h hab
  have hRL : R ≤ L := hRS.trans (map_subtype_le _)
  let q := QuotientGroup.mk' (pCore 2 L)
  let U := T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
  let : Fact (IsPGroup 2 U) := ⟨U.isPGroup'⟩
  have hfU (x : R) : q (inclusion hRL x) ∈ (U : Subgroup (L ⧸ pCore 2 L)) := by
    obtain ⟨t,ht,he⟩ := hRS x.property
    have he' : t = inclusion hRL x := Subtype.ext he
    exact mem_map_of_mem q (he' ▸ ht)
  let f : R →* U := (q.comp (inclusion hRL)).codRestrict U hfU
  have hf := frattini_map_le_of_isPGroup (p := 2) f
  have ho := marked_unitary_frattini_upper hn mark U
  have hz := source_rankOne_center_image_omega h hB d hc hb Mb T hT
  rintro x ⟨y,hy,rfl⟩
  have hx := ho (mem_map_of_mem (U : Subgroup (L ⧸ pCore 2 L)).subtype
    (hf (mem_map_of_mem f hy)))
  change q (inclusion hRL y) ∈ omegaCenterIn (U : Subgroup (L ⧸ pCore 2 L)) at hx
  change ((Z (family P) a).subgroupOf L).map q = omegaCenterIn (U : Subgroup (L ⧸ pCore 2 L)) at hz
  rw [←hz] at hx
  obtain ⟨z,hz,he⟩ := hx
  have hker : inclusion hRL y * z⁻¹ ∈ pCore 2 L := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (inclusion hRL y * z⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hq : (y : G) * (z : G)⁻¹ ∈ Q (family P) b := by
    rw [←localGroup_core_eq (family P) d b]
    exact mem_map_of_mem L.subtype hker
  have hh := (Z (family P) a ⊔ Q (family P) b).mul_mem
    ((show Q (family P) b ≤ Z (family P) a ⊔ Q (family P) b from le_sup_right) hq)
    ((show Z (family P) a ≤ Z (family P) a ⊔ Q (family P) b from le_sup_left) hz)
  simpa only [Subgroup.subtype_apply,inv_mul_cancel_right] using hh

private theorem normalized_subgroup_le_neighbor_intersection
    (d : EarlierLocalTheorems (family P)) {a b : Vertex (family P)}
    (hab : (graph (family P)).Adj a b) (N : Subgroup G)
    (hn : d.localGroup a ≤ normalizer (N : Set G)) (hle : N ≤ Q (family P) b) :
    N ≤ neighborCoreIntersection (family P) a := by
  intro x hx
  apply mem_iInf.mpr
  intro w
  obtain ⟨t,ht,htb⟩ := d.transitive a ⟨b,hab⟩ w
  have hx' := le_normalizer_iff.mp hn t⁻¹ ((d.localGroup a).inv_mem ht) x hx
  have hm := mem_map_of_mem (MulAut.conj t).toMonoidHom (hle hx')
  rw [←Q_translate,htb] at hm
  simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,mul_assoc,
    mul_inv_cancel,inv_mul_cancel,one_mul,mul_one,mul_inv_cancel_left] using hm

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile


namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem elementary_quotient_of_elementary_supplement (A N S : Subgroup G)
    [IsElementaryAbelian 2 A] [(N.subgroupOf S).Normal] (hS : S = A ⊔ N) :
    IsElementaryAbelian 2 (S ⧸ N.subgroupOf S) := by
  have hAS : A ≤ S := hS ▸ le_sup_left
  have hNS : N ≤ S := hS ▸ le_sup_right
  let q := QuotientGroup.mk' (N.subgroupOf S)
  let f := q.comp (inclusion hAS)
  apply IsElementaryAbelian.of_surjective f
  apply MonoidHom.range_eq_top.mp
  have hh := congrArg (Subgroup.map q) (show A.subgroupOf S ⊔ N.subgroupOf S = ⊤ by
    rw [←subgroupOf_sup hAS hNS,←hS,subgroupOf_self])
  rw [Subgroup.map_sup,map_top_of_surjective q (QuotientGroup.mk'_surjective _),
    show (N.subgroupOf S).map q = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq] at hh
  rw [MonoidHom.range_comp]
  rwa [inclusion_range]

theorem source_unitary_alpha_center_le_frattini_from_marking
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
    Z (family P) a ≤ (frattini (Q (family P) a)).map (Q (family P) a).subtype := by
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
  let R := Q (family P) a
  let N := (frattini R).map R.subtype
  let A := Z (family P) a
  let C := Q (family P) b
  let : Finite R := Finite.of_injective (inclusion (Q_le_stabilizer _ a)) (inclusion_injective _)
  let : Fact (IsPGroup 2 R) := ⟨isPGroup_pCoreIn 2 _⟩
  have hnN : stabilizer (family P) a ≤ normalizer (N : Set G) :=
    (stabilizer_normalizes_Q _ a).trans (normalizer_le_normalizer_characteristic_image R (frattini R))
  have hnA := stabilizer_normalizes_Z (family P) a
  have hupper := alpha_frattini_le_center_join_beta h hB d hc hb Mb hn mark
  change N ≤ A ⊔ C at hupper
  have hmin := source_unitary_alpha_center_minimal h hB hS d hc hb hcomm hbc hac Ma hn mark (N ⊓ A) inf_le_right
    (((d.local_le a).trans (le_inf hnN hnA)).trans inf_normalizer_le_normalizer_inf)
  rcases hmin with hz | hz
  · have hCL : C ≤ stabilizer (family P) a := (source_Z_Q_U h b).2.trans
      ((ballKernel_one_le_edge _ hab.symm).trans inf_le_right)
    have hZbA : Z (family P) b ≤ A := by
      rw [critical_end_center_of_commuting (family P) h.generate
        (fun v => (source_Z_Q_U h v).1) (fun v => (source_Z_Q_U h v).2) hc hcomm
        (d.localGroup b) (d.sylow_or_center b)]
      exact local_omega_le_neighbor_Z h d hab.symm
    have hder : ⁅C,C⁆ ≤ A :=
      (source_unitary_beta_core_layers h hB hS d hc hb hcomm hbc hac Ma hn mark).2.1.trans hZbA
    have hcommA : ⁅A ⊔ C,C⁆ ≤ A := commutator_sup_le_of_relative_normal
      (stabilizer (family P) a) A C C A hnA (Z_le_stabilizer _ a) hCL
      (le_normalizer_iff_commutator_le_left.mp (hCL.trans hnA)) hder
    have hNC : ⁅N,C⁆ = ⊥ := bot_unique ((le_inf
      (le_normalizer_iff_commutator_le_left.mp (hCL.trans hnN))
      ((commutator_mono hupper le_rfl).trans hcommA)).trans hz.le)
    have hNC' : N ≤ C :=
      (le_inf ((map_subtype_le _).trans ((source_Z_Q_U h a).2.trans
        ((ballKernel_one_le_edge _ hab).trans inf_le_right)))
        (commutator_eq_bot_iff_le_centralizer.mp hNC)).trans
          (source_core_selfCentralizing_in_vertex h b)
    have hNbot : N = ⊥ := bot_unique ((normalized_subgroup_le_neighbor_intersection d hab N
      ((d.local_le a).trans hnN) hNC').trans
        (source_unitary_alpha_neighbor_core_eq_bot h hB hS d hc hb hcomm hbc hac Ma hn mark).le)
    have hphi : frattini R = ⊥ :=
      ((frattini R).map_eq_bot_iff_of_injective R.subtype_injective).mp hNbot
    let := (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hphi
    obtain ⟨hN,hnot⟩ := hne
    let := hN
    exact False.elim (hnot (elementary_quotient_of_elementary_supplement R C _
      (source_core_product_and_alpha_on_path h hB d hc hb hcomm hbc hac Ma Mb
        ht p hp ha hbp hcp).1))
  · exact hz ▸ inf_le_left

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
private theorem alpha_frattini_quotient_lower
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m)) :
    Nat.card (Z (family P) a) ≤ Nat.card (Q (family P) a ⧸ frattini (Q (family P) a)) := by
  let := finite_endpoints h
  obtain ⟨hfield,n,hn,hi,hq⟩ := source_unitary_field_parameters_from_marking h hB hS d hc hb hcomm hbc hac Ma hm mark
  obtain ⟨k,_,_,hk,⟨ea⟩⟩ := hi
  let : Fintype k := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hk)
  let ep : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  have ho := (source_unitary_center_seed_pair_orders h hB hS d hc hb hcomm hbc hac Ma hm mark).2.2.1
  have hsize : Nat.card (Z (family P) a) = Nat.card k ^ 2 := by
    rw [←hfield,←hq,←pow_two] at ho
    rwa [hk]
  let L := d.localGroup a
  let R := Q (family P) a
  let : Finite L := Finite.of_injective (inclusion (d.local_le a)) (inclusion_injective _)
  let : (L.subgroupOf (stabilizer (family P) a)).Normal :=
    (normal_subgroupOf_iff_le_normalizer (d.local_le a)).mpr
      (localGroup_normalized (family P) d a)
  have hself : centralizer (pCore 2 L : Set L) ≤ pCore 2 L :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe (d.local_le a))).mp
      (normal_core_selfCentralizing (source_vertex_core_selfCentralizing h a)
        (L.subgroupOf (stabilizer (family P) a)))
  have hlarge : 3 < Nat.card k := by
    rw [hk]
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    norm_num at hh
    omega
  have hl := Representation.SL2.characteristic_two_frattini_card_lower hself (ea.trans ep.symm) hlarge
  let eR : pCore 2 L ≃* R :=
    ((pCore 2 L).equivMapOfInjective L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr (localGroup_core_eq (family P) d a))
  have hcard := Nat.card_congr (QuotientGroup.congr _ _ eR (frattini_map_equiv eR)).toEquiv
  rwa [hcard,←hsize] at hl

theorem source_unitary_alpha_frattini_from_marking
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
    (frattini (Q (family P) a)).map (Q (family P) a).subtype = Z (family P) a ∧
      ∃ hN : ((Z (family P) a).subgroupOf (Q (family P) a)).Normal, letI := hN
        IsElementaryAbelian 2 (Q (family P) a ⧸ (Z (family P) a).subgroupOf (Q (family P) a)) := by
  let := finite_endpoints h
  let R := Q (family P) a
  let N := (frattini R).map R.subtype
  let A := Z (family P) a
  let : Finite R := Finite.of_injective (inclusion (Q_le_stabilizer _ a)) (inclusion_injective _)
  have hl := source_unitary_alpha_center_le_frattini_from_marking h hB hS d hc hb hcomm hbc hac Ma hn mark
  have hlo := alpha_frattini_quotient_lower h hB hS d hc hb hcomm hbc hac Ma hn mark
  have horders := source_unitary_center_seed_pair_orders h hB hS d hc hb hcomm hbc hac Ma hn mark
  have hZb := source_unitary_center_card_from_marking h hB hS d hc hb hcomm hbc hac Ma hn mark
  have hβ := horders.1.symm.trans hZb
  have hfield := (source_unitary_field_parameters_from_marking h hB hS d hc hb hcomm hbc hac Ma hn mark).1
  have hZa : Nat.card A = 2^(4*n) := by
    calc
      Nat.card A = (2^n)^2 * (2^n)^2 := by rw [horders.2.2.1,hfield,hβ]
      _ = 2^(4*n) := by rw [←pow_add,←pow_mul]; congr 1; omega
  have hRa := (source_unitary_core_orders_from_marking h hB hS d hc hb hcomm hbc hac Ma hn mark).2.2.2.1
  have hcount := (frattini R).card_mul_index
  rw [index_eq_card] at hcount
  have hφ : Nat.card N = Nat.card (frattini R) := card_map_of_injective R.subtype_injective
  have hRcard : Nat.card R = Nat.card A * Nat.card A := by
    rw [hRa,hZa,←pow_add]; congr 1; omega
  have hpos : 0 < Nat.card A := by rw [hZa]; positivity
  have hu : Nat.card N ≤ Nat.card A := by
    rw [hφ]
    have hmul := Nat.mul_le_mul_left (Nat.card (frattini R)) hlo
    rw [hcount,hRcard] at hmul
    nlinarith
  let : Finite A := Finite.of_injective
    (inclusion ((source_Z_Q_U h a).1.trans (map_subtype_le _))) (inclusion_injective _)
  let : Finite N := Finite.of_injective
    (inclusion (show N ≤ R from map_subtype_le _)) (inclusion_injective _)
  change A ≤ N at hl
  have heq : N = A := (eq_of_le_of_card_ge hl hu).symm
  have hN : (A.subgroupOf R).Normal := normal_subgroupOf_of_le_normalizer
    ((Q_le_stabilizer _ a).trans (stabilizer_normalizes_Z (family P) a))
  refine ⟨heq,hN,?_⟩
  let := hN
  apply elementary_quotient_of_frattini_le (G := R) (show IsPGroup 2 R from isPGroup_pCoreIn 2 _) (A.subgroupOf R)
  intro x hx
  exact heq ▸ mem_map_of_mem R.subtype hx

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
