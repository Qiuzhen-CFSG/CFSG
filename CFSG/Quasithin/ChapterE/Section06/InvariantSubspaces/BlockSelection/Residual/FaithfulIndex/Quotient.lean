module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.FaithfulIndex.Contracts
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The index consequence of the normal-block quotient-rank bound

Choose a Sylow three-subgroup P of N containing the cubic actor outside H.
Assume its elements normalize L, and set J = LP. The quotient J/L is a
three-group. The explicit normal-block rank input makes this quotient cyclic.
A nontrivial subgroup of a cyclic three-group contains every element of
order three, so the actor outside H forces (H ∩ J)/L to be trivial.
Thus P ∩ H lies in L. Relative normality of H in N identifies P ∩ H as a
Sylow subgroup of H, giving index prime to three.

The proof does not assume normality of L in H, a residual identity, or
containment of a Sylow three-subgroup in L. The last containment is its
conclusion. The normal-block quotient-rank calculation is still an input.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
the proof of E.6.14 on printed p.251 (PDF p.262).
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
private theorem threeGroup_subgroup_eq_bot_of_omits_three
    {R : Type*} [Group R] [Finite R] (hp : IsPGroup 3 R)
    (hr : primeRank 3 R ≤ 1) (B : Subgroup R)
    {x : R} (hx : orderOf x = 3) (hxB : x ∉ B) : B = ⊥ := by
  let : IsCyclic R := hp.isCyclic_of_odd_of_elementary_card_le (by decide)
    (fun E hE => by
      let := hE
      exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hr E)
  let : CommGroup R := IsMulCommutative.instCommGroup
  by_contra hn
  obtain ⟨b, hb, hb1⟩ := B.bot_or_exists_ne_one.resolve_left hn
  let a := b ^ (orderOf b / 3)
  have ha : orderOf a = 3 :=
    orderOf_pow_orderOf_div (Nat.ne_of_gt (orderOf_pos b)) (hp.dvd_orderOf hb1)
  have haB : a ∈ B := B.pow_mem hb _
  let E := zpowers a
  let : IsElementaryAbelian 3 E :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (ha ▸ pow_orderOf_eq_one a)
  have hxc : E ≤ centralizer ({x} : Set R) := by
    intro e he
    exact mem_centralizer_singleton_iff.mpr (mul_comm _ _)
  have hxE : x ∉ E := fun hm => hxB ((zpowers_le.mpr haB) hm)
  have hc : Nat.card E = 3 ^ 1 := by simpa only [pow_one] using (Nat.card_zpowers a).trans ha
  have hbound := IsElementaryAbelian.primeRank_ge_of_fixed_join E x hx hxE hxc hc
  omega

private theorem subgroup_eq_of_three_quotient
    {R : Type*} [Group R] [Finite R] (L H : Subgroup R) [L.Normal]
    (hLH : L ≤ H) (hp : IsPGroup 3 (R ⧸ L)) (hr : primeRank 3 (R ⧸ L) ≤ 1)
    {x : R} (hx : orderOf x = 3) (hxH : x ∉ H) : H = L := by
  let q := QuotientGroup.mk' L
  have hnot : q x ∉ H.map q := by
    intro he
    have hh : x ∈ (H.map q).comap q := he
    rw [comap_map_eq_self (show q.ker ≤ H by simpa only [q, QuotientGroup.ker_mk'] using hLH)] at hh
    exact hxH hh
  have hne : q x ≠ 1 := fun he => hnot (he ▸ (H.map q).one_mem)
  have ho : orderOf (q x) = 3 := by
    have hd : orderOf (q x) ∣ 3 := hx ▸ orderOf_map_dvd q x
    exact (Nat.dvd_prime Nat.prime_three).mp hd |>.resolve_left (fun he => hne (orderOf_eq_one_iff.mp he))
  have hbot := threeGroup_subgroup_eq_bot_of_omits_three hp hr (H.map q) ho hnot
  apply le_antisymm _ hLH
  have hh : H ≤ q.ker := by rwa [Subgroup.map_eq_bot_iff] at hbot
  simpa only [q, QuotientGroup.ker_mk'] using hh

variable {G : Type*} [Group G] [Finite G]

/-- An external cubic actor and the intrinsic quotient-rank bound exclude
the three-part of the relative index. -/
theorem three_index_coprime_of_normalized_sylow_quotient
    (hq : NormalChiZeroQuotientRankInput G)
    {N H L : Subgroup G} (hHN : H ≤ N) (hLH : L ≤ H)
    (hnH : (H.subgroupOf N).Normal) (hL : ChapterC.IsChiZeroBlock L)
    (hrN : primeRank 3 N ≤ 2)
    (hnL : ∀ y ∈ N, (∃ k, orderOf y ∣ 3 ^ k) → y ∈ normalizer (L : Set G))
    {x : G} (hxN : x ∈ N) (hx : orderOf x = 3) (hxH : x ∉ H) :
    Nat.Coprime 3 (L.relIndex H) := by
  let := hnH
  let xN : N := ⟨x, hxN⟩
  have hxNo : orderOf xN = 3 := (Subgroup.orderOf_coe xN).symm.trans hx
  have hxp : IsPGroup 3 (zpowers xN) :=
    IsPGroup.of_card ((Nat.card_zpowers xN).trans (hxNo.trans (pow_one 3).symm))
  obtain ⟨P, hP⟩ := hxp.exists_le_sylow
  let P₀ : Subgroup G := (P : Subgroup N).map N.subtype
  have hP₀N : P₀ ≤ N := map_subtype_le _
  have hP₀ : IsPGroup 3 P₀ := P.isPGroup'.map N.subtype
  have hxP₀ : x ∈ P₀ := mem_map.mpr ⟨xN, hP (mem_zpowers xN), rfl⟩
  have hP₀L : P₀ ≤ normalizer (L : Set G) := by
    intro y hy
    obtain ⟨k, hk⟩ := hP₀.exists_orderOf_dvd_pow ⟨y, hy⟩
    apply hnL y (hP₀N hy)
    exact ⟨k, (Subgroup.orderOf_coe (⟨y, hy⟩ : P₀)).symm ▸ hk⟩
  let J : Subgroup G := L ⊔ P₀
  have hLJ : L ≤ J := le_sup_left
  have hPJ : P₀ ≤ J := le_sup_right
  have hJN : J ≤ N := sup_le (hLH.trans hHN) hP₀N
  let : (L.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hP₀L)
  have hgen : L.subgroupOf J ⊔ P₀.subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup hLJ hPJ]
    exact subgroupOf_self J
  have hquotP : IsPGroup 3 (J ⧸ L.subgroupOf J) :=
    isPGroup_quotient_of_sup_eq_top _ _ hP₀.comap_subtype hgen
  have hquotR : primeRank 3 (J ⧸ L.subgroupOf J) ≤ 1 :=
    hq J L hLJ inferInstance hL
      ((Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hJN)
        (inclusion_injective hJN)).trans hrN) hquotP
  let xJ : J := ⟨x, hPJ hxP₀⟩
  have hxJo : orderOf xJ = 3 := (Subgroup.orderOf_coe xJ).symm.trans hx
  have he : H.subgroupOf J = L.subgroupOf J :=
    subgroup_eq_of_three_quotient _ _ (subgroupOf_mono J hLH) hquotP hquotR
      hxJo hxH
  obtain ⟨S, hS⟩ := P.exists_subgroupOf_eq_of_normal (H.subgroupOf N)
  have hSL : (S : Subgroup (H.subgroupOf N)) ≤
      (L.subgroupOf N).subgroupOf (H.subgroupOf N) := by
    intro y hy
    have hyP : (y : N) ∈ (P : Subgroup N) := by rw [hS] at hy; exact hy
    have hyP₀ : ((y : N) : G) ∈ P₀ := mem_map.mpr ⟨y, hyP, rfl⟩
    have hyH : (⟨((y : N) : G), hPJ hyP₀⟩ : J) ∈ H.subgroupOf J := y.property
    rw [he] at hyH
    exact hyH
  have hi : Nat.Coprime 3 ((L.subgroupOf N).relIndex (H.subgroupOf N)) :=
    (Nat.prime_three.coprime_iff_not_dvd.mpr S.not_dvd_index).coprime_dvd_right
      (index_dvd_of_le hSL)
  simpa only [relIndex_subgroupOf hHN] using hi

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
