module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.NeighborCoreCenter

/-!
# Exact Chapter 11 center, seed and pair orders

The neighboring-core argument supplies |Z_beta|=q_beta. The two mixed
center intersections identify the kernel of the opposite seed in the alpha
quotient with Z_beta. Conjugacy counts the first seed, the critical-center
index counts Z_alpha, and the normalized two-seed product counts V_beta.
Thus the literal source indices give |Z_alpha|=q_alpha q_beta² and
|V_beta|=q_alpha² q_beta for the complete beta catalogue.

The Suzuki and both unitary quotient markings evaluate the beta index
in the original Sylow omega-center, including the small source parameters.
No core-order or natural-module premise is assumed. The Suzuki core upper
bound and the remaining (11.8) layers remain subsequent source duties.
ReducedCenterOrders transports these results through the original inclusion.
Source: DGS85, Groups and Graphs (1985), (11.6)(c), (11.3)(a,b) and the
count used in (11.8), printed pp.168--176.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem core_sup_index (Q C : Subgroup G)
    (hCQ : C ≤ normalizer (Q : Set G)) : Q.relIndex (Q ⊔ C) = Q.relIndex C := by
  let H := Q ⊔ C
  let : (Q.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le Q.le_normalizer hCQ)
  have he := relIndex_sup_left (C.subgroupOf H) (Q.subgroupOf H)
  rw [←subgroupOf_sup le_sup_left le_sup_right,relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right] at he
  exact he

private theorem normalized_product_card (A C : Subgroup G)
    (hn : C ≤ normalizer (A : Set G)) :
    Nat.card A * Nat.card C = Nat.card (A ⊓ C : Subgroup G) * Nat.card (A ⊔ C : Subgroup G) := by
  have hi : A.relIndex (A ⊔ C) = (A ⊓ C).relIndex C :=
    (core_sup_index A C hn).trans (inf_relIndex_right A C).symm
  have hH := relIndex_mul_relIndex (⊥ : Subgroup G) A (A ⊔ C) bot_le le_sup_left
  have hC := relIndex_mul_relIndex (⊥ : Subgroup G) (A ⊓ C) C bot_le inf_le_right
  simp only [relIndex_bot_left] at hH hC
  rw [hi] at hH
  rw [←hC,←hH]
  ac_rfl

/-- Both centers, the actual seed, and its conjugate pair span have the source orders. -/
theorem source_center_seed_pair_orders_on_escaping_path
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
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices) :
    let qα := (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b)
    let qβ := (Q (family P) b).relIndex (Z (family P) a)
    Nat.card (Z (family P) b) = qβ ∧
      Nat.card (Z (family P) a ⊓ Q (family P) b : Subgroup G) = qα * qβ ∧
      Nat.card (Z (family P) a) = qα * qβ^2 ∧
      Nat.card (pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)) = qα^2 * qβ := by
  let := finite_endpoints h
  let : Finite (Z (family P) b) := Finite.of_injective
    (inclusion (Z_le_stabilizer _ b)) (inclusion_injective _)
  let qα := (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b)
  let qβ := (Q (family P) b).relIndex (Z (family P) a)
  let E := Z (family P) a ⊓ Q (family P) b
  let C := Z (family P) c ⊓ Q (family P) b
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨n,hn,hi⟩ := (source_core_product_and_alpha_on_path h hB d hc hb hcomm
    hbc hac Ma Mb ht p hp ha hbp hcp).2
  obtain ⟨k,_,_,hk,⟨ea⟩⟩ := hi
  let : Fintype k := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hk)
  let ep : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  have hcent := source_linear_rankOne_center_intersections h hB d hc hb hcomm hbc hac Ma Mb (ea.trans ep.symm)
  have hz : Nat.card (Z (family P) b) = qβ :=
    source_center_card_eq_critical_index_on_escaping_path h hB hS d hc hb hcomm
      hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
  have hic : Q (family P) a ⊓ C = Z (family P) b := by
    change Q (family P) a ⊓ (Z (family P) c ⊓ Q (family P) b) = _
    rw [←inf_assoc,hcent.2.1,inf_eq_left.mpr ((source_Z_Q_U h b).1.trans (map_subtype_le _))]
  have hZC : Z (family P) b ≤ C := hic ▸ inf_le_right
  have hidx : (Z (family P) b).relIndex C = qα := by
    rw [←hic,inf_relIndex_right]
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup G) (Z (family P) b) C bot_le hZC
  rw [relIndex_bot_left,relIndex_bot_left,hidx,hz] at hcount
  obtain ⟨t,_,_,_,he⟩ := source_neighbor_conjugate h hab hbc
  have hconj : Nat.card C = Nat.card E := by
    change Nat.card (Z (family P) c ⊓ Q (family P) b : Subgroup G) = _
    rw [←he,card_map_of_injective (MulAut.conj t).injective]
  have hE : Nat.card E = qα * qβ := by
    rw [hconj] at hcount
    exact hcount.symm.trans (Nat.mul_comm _ _)
  have hC : Nat.card C = qα * qβ := hconj.trans hE
  have hcount' := relIndex_mul_relIndex (⊥ : Subgroup G) E (Z (family P) a) bot_le inf_le_left
  have hidx' : E.relIndex (Z (family P) a) = qβ := inf_relIndex_left _ _
  rw [relIndex_bot_left,relIndex_bot_left,hidx',hE] at hcount'
  have hZa : Nat.card (Z (family P) a) = qα * qβ^2 := hcount'.symm.trans (by ring)
  have hnC : C ≤ normalizer (E : Set G) := inf_le_right.trans
    ((le_inf (source_adjacent_core_normalizes_center h hab)
      (Q (family P) b).le_normalizer).trans inf_normalizer_le_normalizer_inf)
  have hprod := normalized_product_card E C hnC
  rw [hE,hC,hcent.2.2.2,hz] at hprod
  refine ⟨hz,hE,hZa,?_⟩
  change Nat.card (E ⊔ C : Subgroup G) = qα^2*qβ
  apply Nat.eq_of_mul_eq_mul_left (show 0 < qβ from hz ▸ Nat.card_pos)
  exact hprod.symm.trans (by ring)

private theorem omega_card_transport {H D : Type*} [Group H] [Group D] [Finite H]
    (e : H ≃* D) (T : Sylow 2 H) :
    Nat.card (omegaCenterIn (T.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup D)) =
      Nat.card (omegaCenterIn (T : Subgroup H)) := by
  change Nat.card (omegaCenterIn ((T : Subgroup H).map e.toMonoidHom)) = _
  rw [←NilesRankOneKernel.omegaCenterIn_map_injective e.toMonoidHom e.injective,
    card_map_of_injective e.injective]

/-- The beta-center order for the actual Suzuki marking, including parameter zero. -/
theorem source_suzuki_center_card_on_escaping_path
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
    (m : ℕ) (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    Nat.card (Z (family P) b) = 2^(2*m+1) := by
  let : Finite (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := Mb.finite
  have hz := source_center_card_eq_critical_index_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
  obtain ⟨Ta,Tb,_,_,_,hidx⟩ := source_core_product_indices_on_path h hB d hc hb hbc hac
    Ma Mb ht p hp ha hbp hcp
  have hm := BenderSuzuki.MatrixGroups.suzukiSylow_omegaCenter_card_index m
    (Tb.mapSurjective (f := eb.toMonoidHom) eb.surjective)
  exact (hz.trans hidx.symm).trans ((omega_card_transport eb Tb).symm.trans hm.1)

/-- The beta-center order retains both projective and full special-unitary
markings, and includes the binary fixed field. -/
theorem source_unitary_center_card_on_escaping_path
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
    (n : ℕ) (hn : 0 < n)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^n)) :
    Nat.card (Z (family P) b) = 2^n := by
  let : Finite (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := Mb.finite
  have hz := source_center_card_eq_critical_index_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
  obtain ⟨Ta,Tb,_,_,_,hidx⟩ := source_core_product_indices_on_path h hB d hc hb hbc hac
    Ma Mb ht p hp ha hbp hcp
  apply (hz.trans hidx.symm).trans
  rcases mark with mark | mark
  · obtain ⟨E,_,_,J,hcard,hconj,⟨eb⟩⟩ := mark
    have hm := BenderSuzuki.MatrixGroups.HermitianForm.SylowOmegaIndex.projective J hn hcard hconj
      (Tb.mapSurjective (f := eb.toMonoidHom) eb.surjective)
    exact (omega_card_transport eb Tb).symm.trans hm.1
  · obtain ⟨E,_,_,J,hcard,hconj,⟨eb⟩⟩ := mark
    have hm := BenderSuzuki.MatrixGroups.HermitianForm.SylowOmegaIndex.special J hn hcard hconj
      (Tb.mapSurjective (f := eb.toMonoidHom) eb.surjective)
    exact (omega_card_transport eb Tb).symm.trans hm.1

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
