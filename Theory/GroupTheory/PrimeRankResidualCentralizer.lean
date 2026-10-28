module

public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.Quasithin.CoprimeRank
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.CubicIntersectionRankLower
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Odd ranks near a normalized factor

An odd-prime Sylow subgroup lies in the two-residual, and a two-group
kernel preserves its prime rank. Commuting subgroups with intersection
of order prime to p contribute independent elementary abelian p-subgroups.
For a normalized factor K, we apply this in the literal quotient by
O₂(K). Their intersection embeds in the centre of K/O₂(K).

A separate three-rank estimate allows a centre of order at most three:
two commuting rank-two factors then produce rank at least three, even
when their intersection is nontrivial. In particular no direct-product
assertion is made for a triple cover.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, combined manuscript (1 March 2004), proof of Lemma 8.2.9,
printed p.720 (PDF p.737). The chapter consumer retains the actual local
solvable residual and the marked quotient model.
-/

public section

open Subgroup
namespace Theory.GroupTheory.ResidualCentralizerRank
variable {G : Type*} [Group G] [Finite G]

/-- Taking the q-residual preserves p-rank when q and p are coprime. -/
theorem primeRank_residual {p q : ℕ} [Fact p.Prime] (hpq : Nat.Coprime q p) :
    primeRank p (pResidual q G) = primeRank p G := by
  apply le_antisymm (primeRank_subgroup_le p _)
  let P : Sylow p G := Classical.choice inferInstance
  have hPR : (P : Subgroup G) ≤ pResidual q G := by
    intro x hx
    apply mem_pResidual_of_orderOf_coprime
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    have hd : orderOf x ∣ p ^ n := by
      have hh := _root_.orderOf_dvd_natCard (⟨x, hx⟩ : (P : Subgroup G))
      rw [Subgroup.orderOf_mk, hn] at hh
      exact hh
    exact (hpq.pow_right n).of_dvd_right hd
  rw [P.primeRank_eq]
  exact primeRank_mono p hPR

/-- A p-subgroup has trivial intersection with a subgroup when that intersection is p-prime. -/
theorem disjoint_of_pGroup_of_coprime_intersection {p : ℕ} [Fact p.Prime]
    (A B : Subgroup G) (hA : IsPGroup p A)
    (hc : Nat.Coprime p (Nat.card (A ⊓ B : Subgroup G))) : Disjoint A B := by
  have hi : IsPGroup p (A ⊓ B : Subgroup G) := hA.to_le inf_le_left
  obtain ⟨n, hn⟩ := hi.exists_card_eq
  have hn0 : n = 0 := by
    by_contra hn0
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hc
      (hn ▸ dvd_pow_self p hn0)
  apply disjoint_iff.mpr
  apply (eq_bot_iff_card _).mpr
  rw [hn, hn0, pow_zero]

/-- Commuting subgroups with p-prime intersection contribute independent p-ranks. -/
theorem primeRank_add_le_of_coprime_intersection {p : ℕ} [Fact p.Prime]
    (A B : Subgroup G) (hcomm : A ≤ centralizer (B : Set G))
    (hcop : Nat.Coprime p (Nat.card (A ⊓ B : Subgroup G))) :
    primeRank p A + primeRank p B ≤ primeRank p G := by
  obtain ⟨E, hE, hEc⟩ := exists_elementaryAbelian_card_primeRank (G := A) (p := p)
  obtain ⟨F, hF, hFc⟩ := exists_elementaryAbelian_card_primeRank (G := B) (p := p)
  let _ := hE
  let _ := hF
  let E' := E.map A.subtype
  let F' := F.map B.subtype
  let _ : IsElementaryAbelian p E' := IsElementaryAbelian.map_subtype
  let _ : IsElementaryAbelian p F' := IsElementaryAbelian.map_subtype
  have hEA : E' ≤ A := map_subtype_le _
  have hFB : F' ≤ B := map_subtype_le _
  have hc : E' ≤ centralizer (F' : Set G) := by
    intro x hx y hy
    exact hcomm (hEA hx) y (hFB hy)
  have hd : Disjoint E' F' := disjoint_of_pGroup_of_coprime_intersection E' F'
    (IsElementaryAbelian.isPGroup p E')
    (hcop.coprime_dvd_right (card_dvd_of_le (inf_le_inf hEA hFB)))
  let _ : IsElementaryAbelian p (E' ⊔ F' : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hc)
  apply IsElementaryAbelian.primeRank_ge_of_card (E' ⊔ F')
  rw [card_sup_eq_mul_of_normalizes_of_disjoint E' F'
    ((le_centralizer_iff.mp hc).trans (centralizer_le_normalizer _)) hd,
    card_map_of_injective A.subtype_injective,
    card_map_of_injective B.subtype_injective, hEc, hFc, pow_add]

omit [Finite G] in
/-- The intersection of commuting subgroups embeds in the centre of either factor. -/
theorem coprime_intersection_of_center (A B : Subgroup G)
    (hcomm : A ≤ centralizer (B : Set G)) {p : ℕ}
    (hcenter : Nat.Coprime p (Nat.card (center B))) :
    Nat.Coprime p (Nat.card (A ⊓ B : Subgroup G)) := by
  let f : (A ⊓ B : Subgroup G) →* center B :=
    { toFun := fun x => ⟨⟨x, x.property.2⟩, by
        apply mem_center_iff.mpr
        intro b
        exact Subtype.ext (hcomm x.property.1 b b.property)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : center B => ((z : B) : G)) h)
  exact hcenter.coprime_dvd_right (card_dvd_of_injective f hf)

/-- A p-prime centre supplies the necessary intersection bound for rank addition. -/
theorem primeRank_add_le_of_center_coprime {p : ℕ} [Fact p.Prime]
    (A B : Subgroup G) (hcomm : A ≤ centralizer (B : Set G))
    (hcenter : Nat.Coprime p (Nat.card (center B))) :
    primeRank p A + primeRank p B ≤ primeRank p G :=
  primeRank_add_le_of_coprime_intersection A B hcomm
    (coprime_intersection_of_center A B hcomm hcenter)

/-- The actual subgroup image under a two-group kernel preserves odd prime ranks. -/
theorem primeRank_map_of_twoGroup_kernel {D : Type*} [Group D] [Finite D]
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (f : G →* D)
    (hk : IsPGroup 2 f.ker) (A : Subgroup G) :
    primeRank p (A.map f) = primeRank p A := by
  have hker : IsPGroup 2 (f.subgroupMap A).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  apply (primeRank_eq_of_surjective_of_coprime p (f.subgroupMap A)
    (f.subgroupMap_surjective A) ?_).symm
  obtain ⟨n, hn⟩ := hker.exists_card_eq
  rw [hn]
  exact (Nat.coprime_two_right.mpr ho).pow_right n

/-- The rank comparison after passing the actual residual and factor through a two-group kernel. -/
theorem primeRank_sum_le_of_residual_images {D : Type*} [Group D] [Finite D]
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (f : G →* D)
    (hk : IsPGroup 2 f.ker) (H K : Subgroup G)
    (hc : ((pResidual 2 H).map H.subtype).map f ≤ centralizer (K.map f : Set D))
    (hi : Nat.Coprime p (Nat.card
      (((pResidual 2 H).map H.subtype).map f ⊓ K.map f : Subgroup D))) :
    primeRank p H + primeRank p K ≤ primeRank p D := by
  have h := primeRank_add_le_of_coprime_intersection
    (((pResidual 2 H).map H.subtype).map f) (K.map f) hc hi
  rw [primeRank_map_of_twoGroup_kernel ho f hk,
    primeRank_map_of_twoGroup_kernel ho f hk,
    ← primeRank_congr p ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective),
    primeRank_residual (Nat.coprime_two_left.mpr ho)] at h
  exact h

omit [Finite G] in
private instance normal_pCoreIn (K : Subgroup G) [K.Normal] : (K.pCoreIn 2).Normal :=
  inferInstanceAs (((pCore 2 K).map K.subtype).Normal)

private noncomputable def normalFactorCoreQuotientEquiv (K : Subgroup G) [K.Normal] :
    (K ⧸ pCore 2 K) ≃* K.map (QuotientGroup.mk' (K.pCoreIn 2)) := by
  let q := QuotientGroup.mk' (K.pCoreIn 2)
  have he : (q.subgroupMap K).ker = pCore 2 K := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact comap_map_eq_self_of_injective K.subtype_injective _
  exact (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (q.subgroupMap K)
      (q.subgroupMap_surjective K))

/-- Residual commutation modulo the normal factor’s two-core gives the rank bound. -/
theorem primeRank_sum_le_of_normal_factor {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (H K : Subgroup G) [K.Normal]
    (hc : ⁅(pResidual 2 H).map H.subtype, K⁆ ≤ K.pCoreIn 2)
    (hz : Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K)))) :
    primeRank p H + primeRank p K ≤ primeRank p G := by
  let q := QuotientGroup.mk' (K.pCoreIn 2)
  have hq : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact isPGroup_pCoreIn 2 K
  have hcomm : ((pResidual 2 H).map H.subtype).map q ≤ centralizer (K.map q : Set _) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hc
  have hz' : Nat.Coprime p (Nat.card (center (K.map q))) := by
    rwa [← Nat.card_congr (centerCongr (normalFactorCoreQuotientEquiv K)).toEquiv]
  exact (primeRank_sum_le_of_residual_images ho q hq H K hcomm
    (coprime_intersection_of_center _ _ hcomm hz')).trans
      (primeRank_quotient_le_of_isTwoGroup p ho _ (isPGroup_pCoreIn 2 K))

/-- A normal factor with cubic centre and three-rank at least two forces the other factor to rank one. -/
theorem three_rank_le_one_of_normal_factor_cubic_center
    (H K : Subgroup G) [K.Normal]
    (hc : ⁅(pResidual 2 H).map H.subtype, K⁆ ≤ K.pCoreIn 2)
    (hz : Nat.card (center (K ⧸ pCore 2 K)) ≤ 3)
    (hK : 2 ≤ primeRank 3 K) (hG : primeRank 3 G ≤ 2) : primeRank 3 H ≤ 1 := by
  let q := QuotientGroup.mk' (K.pCoreIn 2)
  let R := ((pResidual 2 H).map H.subtype).map q
  let B := K.map q
  have hq : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact isPGroup_pCoreIn 2 K
  have hcomm : R ≤ centralizer (B : Set _) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hc
  have hR : primeRank 3 R = primeRank 3 H := by
    rw [primeRank_map_of_twoGroup_kernel (by decide) q hq,
      ← primeRank_congr 3 ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective),
      primeRank_residual (by decide : Nat.Coprime 2 3)]
  have hB : primeRank 3 B = primeRank 3 K :=
    primeRank_map_of_twoGroup_kernel (by decide) q hq K
  have hi : Nat.card (R ⊓ B : Subgroup _) ≤ 3 := by
    let f : (R ⊓ B : Subgroup _) →* center B :=
      { toFun := fun x => ⟨⟨x, x.property.2⟩, by
          apply mem_center_iff.mpr
          intro b
          exact Subtype.ext (hcomm x.property.1 b b.property)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := by
      intro x y h
      exact Subtype.ext (congrArg (fun z : center B => ((z : B) : G ⧸ K.pCoreIn 2)) h)
    have hcard := Nat.card_le_card_of_injective f hf
    rw [← Nat.card_congr (centerCongr (normalFactorCoreQuotientEquiv K)).toEquiv] at hcard
    exact hcard.trans hz
  by_contra! h
  have hh := three_le_primeRank_of_cubic_intersection R B hcomm hi
    (by omega : 2 ≤ primeRank 3 R) (hB ▸ hK)
  have hu := (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _
    (isPGroup_pCoreIn 2 K)).trans hG
  omega

private theorem residual_commutator_subgroupOf (H K : Subgroup G)
    (hc : ⁅(pResidual 2 H).map H.subtype, K⁆ ≤ K.pCoreIn 2) :
    ⁅(pResidual 2 (H.subgroupOf (H ⊔ K))).map (H.subgroupOf (H ⊔ K)).subtype,
      K.subgroupOf (H ⊔ K)⁆ ≤ (K.subgroupOf (H ⊔ K)).pCoreIn 2 := by
  let J := H ⊔ K
  let e := subgroupOfEquivOfLe (show K ≤ J from le_sup_right)
  apply (map_le_map_iff_of_injective J.subtype_injective).mp
  rw [map_commutator_embedded_pResidual, map_subgroupOf_eq_of_le le_sup_left,
    map_subgroupOf_eq_of_le le_sup_right]
  have he : J.subtype.comp (K.subgroupOf J).subtype = K.subtype.comp e.toMonoidHom := rfl
  change ⁅(pResidual 2 H).map H.subtype, K⁆ ≤
    ((pCore 2 (K.subgroupOf J)).map (K.subgroupOf J).subtype).map J.subtype
  rw [map_map, he, ← map_map, pCore_map_iso]
  exact hc

/-- The relative version inside H K; ambient normality of K is unnecessary. -/
theorem primeRank_sum_le_of_normalized_factor {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (H K : Subgroup G) (hn : H ≤ normalizer (K : Set G))
    (hc : ⁅(pResidual 2 H).map H.subtype, K⁆ ≤ K.pCoreIn 2)
    (hz : Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K)))) :
    primeRank p H + primeRank p K ≤ primeRank p (H ⊔ K : Subgroup G) := by
  let J := H ⊔ K
  let eH := subgroupOfEquivOfLe (show H ≤ J from le_sup_left)
  let eK := subgroupOfEquivOfLe (show K ≤ J from le_sup_right)
  let _ : (K.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le hn K.le_normalizer)
  let e := QuotientGroup.congr (pCore 2 (K.subgroupOf J)) (pCore 2 K) eK
    (pCore_map_iso 2 eK)
  have hz' : Nat.Coprime p (Nat.card (center
      (K.subgroupOf J ⧸ pCore 2 (K.subgroupOf J)))) := by
    rwa [Nat.card_congr (centerCongr e).toEquiv]
  have h := primeRank_sum_le_of_normal_factor ho (H.subgroupOf J) (K.subgroupOf J)
    (residual_commutator_subgroupOf H K hc) hz'
  rwa [primeRank_congr p eH, primeRank_congr p eK] at h

/-- The cubic-centre bound in the actual subgroup generated by H and K. -/
theorem three_rank_le_one_of_normalized_factor_cubic_center
    (H K : Subgroup G) (hn : H ≤ normalizer (K : Set G))
    (hc : ⁅(pResidual 2 H).map H.subtype, K⁆ ≤ K.pCoreIn 2)
    (hz : Nat.card (center (K ⧸ pCore 2 K)) ≤ 3)
    (hK : 2 ≤ primeRank 3 K) (hG : primeRank 3 (H ⊔ K : Subgroup G) ≤ 2) :
    primeRank 3 H ≤ 1 := by
  let J := H ⊔ K
  let eH := subgroupOfEquivOfLe (show H ≤ J from le_sup_left)
  let eK := subgroupOfEquivOfLe (show K ≤ J from le_sup_right)
  let _ : (K.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le hn K.le_normalizer)
  let e := QuotientGroup.congr (pCore 2 (K.subgroupOf J)) (pCore 2 K) eK
    (pCore_map_iso 2 eK)
  have hz' : Nat.card (center (K.subgroupOf J ⧸ pCore 2 (K.subgroupOf J))) ≤ 3 := by
    rwa [Nat.card_congr (centerCongr e).toEquiv]
  have h := three_rank_le_one_of_normal_factor_cubic_center
    (H.subgroupOf J) (K.subgroupOf J) (residual_commutator_subgroupOf H K hc) hz'
    (by rwa [primeRank_congr 3 eK]) hG
  rwa [primeRank_congr 3 eH] at h

end Theory.GroupTheory.ResidualCentralizerRank
