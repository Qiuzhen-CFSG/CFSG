module
public import Theory.GroupTheory.TwoOrbitThree.Quotient

/-!
# Odd-prime index of a two-component orbit

Two commuting centerless factors divisible by p use both ranks in an ambient
group of p-rank at most two. Their centralizer therefore has order prime to p.
If their outer groups also have order prime to p, conjugation gives a product
of prime-to-p index. For odd p this conclusion passes through an index-two
normalizer and the literal ambient two-core quotient.

This is the outer-group branch of Aschbacher--Smith 1.2.2(a), printed p.504;
the A₅ application uses p = 5 in the replacement argument of D.3.21, p.206.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Theory.GroupTheory.TwoOrbitOddPrime
variable {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]

private theorem center_bot_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center A = ⊥) : center B = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have h : e.symm x ∈ center A := ((centerCongr e).symm ⟨x,hx⟩).property
  have he : e.symm x = 1 := by simpa only [hz,mem_bot] using h
  exact e.symm.map_eq_one_iff.mp he

private theorem rank_pos_of_dvd {A : Type*} [Group A] [Finite A]
    (hd : p ∣ Nat.card A) : 1 ≤ primeRank p A := by
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' p hd
  let : IsElementaryAbelian p (zpowers x) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hx ▸ pow_orderOf_eq_one x)
  by_contra hn
  have hh := (primeRank_le_iff_elementary_card_le A (p := p) (n := 0)).mp
    (by omega) (zpowers x) inferInstance
  rw [Nat.card_zpowers,hx,pow_zero] at hh
  have := (Fact.out : p.Prime).one_lt
  omega

private theorem centralizer_join_coprime (L M : Subgroup G)
    (hcomm : ⁅L,M⁆ = ⊥) (hL : center L = ⊥) (hM : center M = ⊥)
    (hdL : p ∣ Nat.card L) (hdM : p ∣ Nat.card M) (hr : primeRank p G ≤ 2) :
    Nat.Coprime p (Nat.card (centralizer ((L ⊔ M : Subgroup G) : Set G))) := by
  have hlow : 2 ≤ primeRank p (L ⊔ M : Subgroup G) := by
    rw [primeRank_sup_eq_add_of_disjoint_commuting L M
      (disjoint_of_commuting_of_center_eq_bot hcomm hL)
      (commutator_eq_bot_iff_le_centralizer.mp hcomm)]
    have := rank_pos_of_dvd p hdL
    have := rank_pos_of_dvd p hdM
    omega
  have heq : primeRank p (L ⊔ M : Subgroup G) = 2 :=
    le_antisymm ((primeRank_subgroup_le p (L ⊔ M)).trans hr) hlow
  obtain ⟨A,hA,hcard⟩ :=
    exists_elementaryAbelian_card_primeRank (G := (L ⊔ M : Subgroup G)) (p := p)
  let := hA
  let E := A.map (L ⊔ M : Subgroup G).subtype
  let : IsElementaryAbelian p E := IsElementaryAbelian.map_subtype
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
  apply prime_not_dvd_card_centralizer_of_full_rank (L ⊔ M) E (map_subtype_le A) _ hr
    (TwoOrbitThree.join_center_eq_bot L M hcomm hL hM)
  simpa only [E,card_map_of_injective (L ⊔ M : Subgroup G).subtype_injective,heq]
    using hcard

/-- The outer-action branch for an arbitrary prime, retaining both factors. -/
theorem outer_join_index_coprime (L M : Subgroup G) [L.Normal] [M.Normal]
    (hcomm : ⁅L,M⁆ = ⊥) (hL : center L = ⊥) (hM : center M = ⊥)
    (hdL : p ∣ Nat.card L) (hdM : p ∣ Nat.card M) (hr : primeRank p G ≤ 2)
    (hoL : Nat.Coprime p (MulAut.innerSubgroup L).index)
    (hoM : Nat.Coprime p (MulAut.innerSubgroup M).index) :
    Nat.Coprime p (L ⊔ M).index := by
  have hC := centralizer_join_coprime p L M hcomm hL hM hdL hdM hr
  have ho : Nat.Coprime p (((MulAut.innerSubgroup L).prod
      (MulAut.innerSubgroup M)).comap (TwoOrbitThree.pairedConjugation L M)).index := by
    have hh : Nat.Coprime p ((MulAut.innerSubgroup L).prod
        (MulAut.innerSubgroup M)).index := by
      simpa only [Subgroup.index_prod] using hoL.mul_right hoM
    exact hh.coprime_dvd_right (by rw [index_comap]; exact relIndex_dvd_index_of_normal _ _)
  rw [TwoOrbitThree.pairedConjugation_comap_inner L M hcomm] at ho
  rw [←relIndex_mul_index (show L ⊔ M ≤ L ⊔ M ⊔
    centralizer ((L ⊔ M : Subgroup G) : Set G) from le_sup_left)]
  exact (hC.coprime_dvd_right (by rw [relIndex_sup_left]; exact relIndex_dvd_card _ _)).mul_right ho

/-- An index-two normalizer adds no factor of an odd prime. -/
theorem outer_pair_index_coprime (hp : p ≠ 2) (L : Subgroup G)
    (hi : (normalizer (L : Set G)).index = 2) (t : G) (hc : ⁅L,L.conjBy t⁆ = ⊥)
    (hz : center L = ⊥) (hd : p ∣ Nat.card L) (hr : primeRank p G ≤ 2)
    (ho : Nat.Coprime p (MulAut.innerSubgroup L).index) :
    Nat.Coprime p (L ⊔ L.conjBy t).index := by
  let N := normalizer (L : Set G)
  let : N.Normal := N.normal_of_index_eq_two hi
  let A := L.subgroupOf N
  let B := (L.conjBy t).subgroupOf N
  have hB := TwoOrbitThree.conjugate_le_normalizer_of_index_two L hi t
  let eA : A ≃* L := subgroupOfEquivOfLe L.le_normalizer
  let eB : B ≃* L := (subgroupOfEquivOfLe hB).trans ((MulAut.conj t).subgroupMap L).symm
  let : A.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : B.Normal := normal_subgroupOf_of_le_normalizer
    (normalizes_conjugate_of_normalizes
      (show t ∈ normalizer (N : Set G) from N.normalizer_eq_top ▸ mem_top t) le_rfl)
  have hcAB : ⁅A,B⁆ = ⊥ := by
    apply map_injective N.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le L.le_normalizer,
      map_subgroupOf_eq_of_le hB,hc,Subgroup.map_bot]
  have hoA : Nat.Coprime p (MulAut.innerSubgroup A).index := by
    change Nat.Coprime p (Nat.card (MulAut.Outer A))
    rw [Nat.card_congr (MulAut.outerCongr eA).toEquiv]
    exact ho
  have hoB : Nat.Coprime p (MulAut.innerSubgroup B).index := by
    change Nat.Coprime p (Nat.card (MulAut.Outer B))
    rw [Nat.card_congr (MulAut.outerCongr eB).toEquiv]
    exact ho
  have hindex := outer_join_index_coprime p A B hcAB
    (center_bot_transport eA.symm hz) (center_bot_transport eB.symm hz)
    (by rwa [Nat.card_congr eA.toEquiv]) (by rwa [Nat.card_congr eB.toEquiv])
    ((primeRank_subgroup_le p N).trans hr) hoA hoB
  have hLN := sup_le L.le_normalizer hB
  have he : (L ⊔ L.conjBy t).subgroupOf N = A ⊔ B := by
    apply map_injective N.subtype_injective
    rw [map_subgroupOf_eq_of_le hLN,Subgroup.map_sup,
      map_subgroupOf_eq_of_le L.le_normalizer,map_subgroupOf_eq_of_le hB]
  rw [←he] at hindex
  rw [←relIndex_mul_index hLN,hi]
  exact hindex.mul_right ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    (fun h => hp ((Nat.prime_two.eq_one_or_self_of_dvd p h).resolve_left
      (Fact.out : p.Prime).ne_one)))

/-- The odd-prime index bound for the original two conjugate C-components. -/
theorem outer_cComponent_pair_index_coprime (hp : p ≠ 2)
    {L : Subgroup G} (hL : L.IsCComponent) [IsQuasisimple (L ⧸ pCore 2 L)]
    (hi : (normalizer (L : Set G)).index = 2) (t : G) (ht : t ∉ normalizer (L : Set G))
    (hz : center (L ⧸ pCore 2 L) = ⊥)
    (hd : p ∣ Nat.card (L ⧸ pCore 2 L)) (hr : primeRank p G ≤ 2)
    (ho : Nat.Coprime p (Nat.card (MulAut.Outer (L ⧸ pCore 2 L)))) :
    Nat.Coprime p (L ⊔ L.conjBy t).index := by
  let _ := pCore_isNilpotent (p := 2) (G := G)
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := L.map q
  let eB := cComponentTwoCoreQuotientEquiv hL
  let : (L ⊔ L.conjBy t).Normal := TwoOrbitThree.pair_normal_of_index_two L hi t ht
  have hindex := outer_pair_index_coprime p hp B
    ((cComponent_normalizer_index_quotient hL _).trans hi) (q t)
    (TwoOrbitThree.quotient_pair_commutes hL t ht) (center_bot_transport eB hz)
    (by rwa [←Nat.card_congr eB.toEquiv])
    ((primeRank_quotient_le_of_isTwoGroup p ((Fact.out : p.Prime).odd_of_ne_two hp)
      _ pCore_isPGroup).trans hr)
    (show Nat.Coprime p (Nat.card (MulAut.Outer B)) from
      (Nat.card_congr (MulAut.outerCongr eB).toEquiv) ▸ ho)
  rw [←TwoOrbitThree.pair_map_quotient L t,index_map,QuotientGroup.ker_mk',
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),index_top,mul_one] at hindex
  have hp2 : Nat.Coprime p 2 := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    (fun h => hp ((Nat.prime_two.eq_one_or_self_of_dvd p h).resolve_left
      (Fact.out : p.Prime).ne_one))
  have hcore : Nat.Coprime p (Nat.card (pCore 2 G)) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_dvd_pow
    exact (hp2.pow_right n).coprime_dvd_right hn
  rw [←relIndex_mul_index (show L ⊔ L.conjBy t ≤ L ⊔ L.conjBy t ⊔ pCore 2 G from le_sup_left)]
  apply Nat.Coprime.mul_right _ hindex
  rw [relIndex_sup_left]
  exact hcore.coprime_dvd_right (relIndex_dvd_card _ _)

end Theory.GroupTheory.TwoOrbitOddPrime
