module

public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.Quasithin.Rank

/-!
# The three-part of the index of a normal C-component

A centerless subgroup containing an elementary nine has centralizer of order
prime to three when the ambient three-rank is at most two. For a normal
subgroup, the kernel of the outer conjugation action is its product with that
centralizer. If the outer group also has order prime to three, the subgroup
has index prime to three. For a C-component the same deduction lifts from
its intrinsic two-core quotient through the ambient two-core.

This is the elementary centerless argument in Aschbacher–Smith,
combined manuscript (1 March 2004), proof of A.3.18, printed pp.51–52.
The result requires the actual outer-group order hypothesis and makes no
classification assumption about exceptional covers or extensions.
-/

public section
open Subgroup
namespace Theory.GroupTheory

private theorem elementaryNine_of_rank {G : Type*} [Group G] [Finite G]
    (h : 2 ≤ primeRank 3 G) :
    ∃ E : Subgroup G, IsElementaryAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  let P : Sylow 3 G := Classical.choice inferInstance
  have hn : ¬ IsCyclic P := by
    intro hc
    have hr := P.primeRank_le_one_of_isCyclic hc
    omega
  obtain ⟨E, _, hcard, he⟩ :=
    P.isPGroup'.exists_normal_elementary_prime_sq_of_odd_not_isCyclic (by decide) hn
  let _ := he
  refine ⟨E.map (P : Subgroup G).subtype, IsElementaryAbelian.map_subtype, ?_⟩
  simpa only [Subgroup.card_map_of_injective (P : Subgroup G).subtype_injective] using hcard

private theorem centralizer_coprime_of_rank {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) (hz : center L = ⊥)
    (hL : 2 ≤ primeRank 3 L) (hG : primeRank 3 G ≤ 2) :
    Nat.Coprime 3 (Nat.card (centralizer (L : Set G))) := by
  obtain ⟨A, hA, hc⟩ := elementaryNine_of_rank hL
  let _ := hA
  let E := A.map L.subtype
  let _ : IsElementaryAbelian 3 E := IsElementaryAbelian.map_subtype
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  apply prime_not_dvd_card_centralizer_of_full_rank L E (map_subtype_le A) _ hG hz
  simpa only [E, Subgroup.card_map_of_injective L.subtype_injective] using hc

private theorem index_coprime_of_centralizer_outer {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) [L.Normal]
    (hC : Nat.Coprime 3 (Nat.card (centralizer (L : Set G))))
    (hO : Nat.Coprime 3 (Nat.card (MulAut.Outer L))) : Nat.Coprime 3 L.index := by
  let f : G →* MulAut.Outer L :=
    (QuotientGroup.mk' (MulAut.innerSubgroup L)).comp MulAut.conjNormal
  have hk : f.ker = L ⊔ centralizer (L : Set G) := by
    change ((QuotientGroup.mk' (MulAut.innerSubgroup L)).comp
      (MulAut.conjNormal : G →* MulAut L)).ker = _
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', MulAut.conjNormal_comap_innerSubgroup]
  have hf : Nat.Coprime 3 f.ker.index := by
    rw [index_ker]
    exact hO.coprime_dvd_right f.range.card_subgroup_dvd_card
  rw [hk] at hf
  rw [← relIndex_mul_index (show L ≤ L ⊔ centralizer (L : Set G) from le_sup_left)]
  apply Nat.Coprime.mul_right _ hf
  rw [relIndex_sup_left]
  exact hC.coprime_dvd_right (relIndex_dvd_card _ _)

private theorem center_bot_of_equiv {Q R : Type*} [Group Q] [Group R]
    (e : Q ≃* R) (hz : center Q = ⊥) : center R = ⊥ := by
  apply eq_bot_iff.mpr
  intro r hr
  have hq : e.symm r ∈ center Q := ((centerCongr e).symm ⟨r, hr⟩).property
  have he : e.symm r = 1 := by simpa only [hz, mem_bot] using hq
  apply mem_bot.mpr
  apply e.symm.injective
  simpa using he

/-- A relatively normal C-component with centerless rank-two quotient and
three-prime outer group has three-prime index. This directly proves the
ordinary residual outcome used from A.3.18 for the binary models. -/
theorem cComponent_index_coprime_three_of_quotient {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) [L.Normal] (hL : L.IsCComponent)
    (hz : center (L ⧸ pCore 2 L) = ⊥)
    (hr : 2 ≤ primeRank 3 (L ⧸ pCore 2 L))
    (hG : primeRank 3 G ≤ 2)
    (ho : Nat.Coprime 3 (Nat.card (MulAut.Outer (L ⧸ pCore 2 L)))) :
    Nat.Coprime 3 L.index := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := L.map q
  let e : (L ⧸ pCore 2 L) ≃* B := cComponentTwoCoreQuotientEquiv hL
  have hzB : center B = ⊥ := center_bot_of_equiv e hz
  have hrB : 2 ≤ primeRank 3 B := by rwa [← primeRank_congr 3 e]
  have hoB : Nat.Coprime 3 (Nat.card (MulAut.Outer B)) := by
    rwa [← Nat.card_congr (MulAut.outerCongr e).toEquiv]
  let _ : B.Normal := (inferInstance : L.Normal).map q (QuotientGroup.mk'_surjective _)
  have hBi := index_coprime_of_centralizer_outer B
    (centralizer_coprime_of_rank B hzB hrB
      ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 G) pCore_isPGroup).trans hG)) hoB
  have hi : B.index = (L ⊔ pCore 2 G).index := by
    dsimp [B, q]
    rw [index_map, QuotientGroup.ker_mk',
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _), index_top, mul_one]
  rw [hi] at hBi
  have hcore : Nat.Coprime 3 (Nat.card (pCore 2 G)) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_dvd_pow
    exact ((by decide : Nat.Coprime 3 2).pow_right n).coprime_dvd_right hn
  rw [← relIndex_mul_index (show L ≤ L ⊔ pCore 2 G from le_sup_left)]
  apply Nat.Coprime.mul_right _ hBi
  rw [relIndex_sup_left]
  exact hcore.coprime_dvd_right (relIndex_dvd_card _ _)

end Theory.GroupTheory
