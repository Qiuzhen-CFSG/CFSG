module
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.GeneralizedFitting.AutomorphismSimple
public import Mathlib.GroupTheory.PGroup
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.GeneralizedFitting.SylowNormalizedComponent

/-!
# Cubic actors on two commuting centerless factors

A cubic normalizing a centerless subgroup with two-group outer automorphism
group differs from an internal cubic by a centralizing cubic. For two commuting
factors, an external cubic would contribute a third independent three-rank.
The component-orbit theorem supplies normalization in odd rank at most two.
Source: Aschbacher--Smith A.3.8(3) and 12.4.8, printed pp.46 and 815.
-/
public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupAction
variable {G : Type*} [Group G]

theorem cubic_inner_shift (K : Subgroup G) (hz : center K = ⊥)
    (hout : IsPGroup 2 (MulAut.Outer K)) {x : G}
    (hxN : x ∈ normalizer (K : Set G)) (hx : x ^ 3 = 1) :
    ∃ k : K, k ^ 3 = 1 ∧
      (k : G)⁻¹ * x ∈ centralizer (K : Set G) ∧ ((k : G)⁻¹ * x) ^ 3 = 1 := by
  let α := K.normalizerMonoidHom ⟨x,hxN⟩
  have hα : α ^ 3 = 1 := by
    rw [← map_pow,show (⟨x,hxN⟩ : normalizer (K : Set G)) ^ 3 = 1 from Subtype.ext hx,map_one]
  let q := QuotientGroup.mk' (MulAut.innerSubgroup K)
  have hq : q α = 1 := by
    have h3 : (q α) ^ 3 = 1 := by rw [← map_pow,hα,map_one]
    by_contra he
    have h2 := hout.dvd_orderOf he
    have hd := h2.trans (orderOf_dvd_of_pow_eq_one h3)
    norm_num at hd
  obtain ⟨k,hk⟩ := (QuotientGroup.eq_one_iff α).mp hq
  have hk3 : k ^ 3 = 1 := by
    apply MulAut.conj_injective_of_center_eq_bot hz
    rw [map_pow,hk,hα,map_one]
  have hc : (k : G)⁻¹ * x ∈ centralizer (K : Set G) := by
    intro a ha
    have he := congrArg (fun β : MulAut K => (β ⟨a,ha⟩ : G)) hk
    change (k : G) * a * (k : G)⁻¹ = x * a * x⁻¹ at he
    calc
      a * ((k : G)⁻¹ * x) = (k : G)⁻¹ * ((k : G) * a * (k : G)⁻¹) * x := by group
      _ = (k : G)⁻¹ * (x * a * x⁻¹) * x := by rw [he]
      _ = ((k : G)⁻¹ * x) * a := by group
  have hkx : Commute (k : G) x := by
    have he := hc k k.property
    change (k : G) * ((k : G)⁻¹ * x) = ((k : G)⁻¹ * x) * (k : G) at he
    have hh := congrArg (fun y : G => (k : G) * y) he
    change (k : G) * x = x * (k : G)
    simpa only [← mul_assoc,mul_inv_cancel,mul_one,one_mul] using hh
  refine ⟨k,hk3,hc,?_⟩
  rw [hkx.inv_left.mul_pow,inv_pow,show (k : G) ^ 3 = 1 from congrArg K.subtype hk3,hx]
  simp

/-- Two commuting centerless factors with nontrivial three-rank absorb every
cubic normalizing both when their outer groups are two-groups and the ambient
three-rank is at most two. -/
theorem cubic_mem_join_of_commuting_centerless [Finite G]
    (K J : Subgroup G) (hzK : center K = ⊥) (hzJ : center J = ⊥)
    (houtK : IsPGroup 2 (MulAut.Outer K)) (houtJ : IsPGroup 2 (MulAut.Outer J))
    (hcomm : K ≤ centralizer (J : Set G))
    (hKr : 1 ≤ primeRank 3 K) (hJr : 1 ≤ primeRank 3 J)
    (hr : primeRank 3 G ≤ 2) {x : G}
    (hxK : x ∈ normalizer (K : Set G)) (hxJ : x ∈ normalizer (J : Set G))
    (hx : x ^ 3 = 1) : x ∈ K ⊔ J := by
  obtain ⟨k,_,hyK,hy3⟩ := cubic_inner_shift K hzK houtK hxK hx
  let y := (k : G)⁻¹ * x
  have hyJ : y ∈ normalizer (J : Set G) :=
    (normalizer (J : Set G)).mul_mem
      ((normalizer (J : Set G)).inv_mem (centralizer_le_normalizer _ (hcomm k.property))) hxJ
  obtain ⟨j,_,hzJc,hz3⟩ := cubic_inner_shift J hzJ houtJ hyJ hy3
  let z := (j : G)⁻¹ * y
  have hzKc : z ∈ centralizer (K : Set G) :=
    (centralizer (K : Set G)).mul_mem
      ((centralizer (K : Set G)).inv_mem (le_centralizer_iff.mp hcomm j.property)) hyK
  by_contra hxout
  have hznotJ : z ∉ J := by
    intro hzmem
    have he : x = (k : G) * ((j : G) * z) := by dsimp [z,y]; group
    rw [he] at hxout
    exact hxout ((K ⊔ J).mul_mem ((le_sup_left : K ≤ K ⊔ J) k.property)
      ((le_sup_right : J ≤ K ⊔ J) (J.mul_mem j.property hzmem)))
  have hzne : z ≠ 1 := fun he => hznotJ (he ▸ J.one_mem)
  have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hzne
  let Z := zpowers z
  have hd : Disjoint J Z := J.disjoint_zpowers_of_prime_order_not_mem z hzo hznotJ
  have hZJ : Z ≤ centralizer (J : Set G) := zpowers_le.mpr hzJc
  have hZK : Z ≤ centralizer (K : Set G) := zpowers_le.mpr hzKc
  have hZr : 1 ≤ primeRank 3 Z := by
    have hn : primeRank 3 Z ≠ 0 := by
      intro he
      apply PrimeRank.eq_zero_iff_not_dvd_card.mp he
      rw [show Nat.card Z = 3 from (Nat.card_zpowers z).trans hzo]
    omega
  have hrank := J.primeRank_sup_eq_add_of_disjoint_commuting Z hd
    (le_centralizer_iff.mp hZJ) 3
  have hsum := ResidualCentralizerRank.primeRank_add_le_of_center_coprime
    (J ⊔ Z) K (sup_le (le_centralizer_iff.mp hcomm) hZK)
    (show Nat.Coprime 3 (Nat.card (center K)) by rw [hzK,card_bot]; decide)
  omega
end Theory.GroupAction

namespace Theory.GroupTheory
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- An order dividing three actor cannot exchange the two possible component
conjugates in a group of odd rank at most two. -/
theorem IsComponent.cubic_normalizes
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p G ≤ 2)
    {K : Subgroup G} (hK : IsComponent G K) {x : G} (hx : x ^ 3 = 1) :
    x ∈ normalizer (K : Set G) := by
  rcases hK.normal_or_index_two_of_odd_rank_le_two hr with hn | hi
  · rw [normalizer_eq_top_iff.mpr hn]
    trivial
  · have h2 := (normalizer (K : Set G)).sq_mem_of_index_two hi x
    apply ((normalizer (K : Set G)).mul_mem_cancel_right h2).mp
    rw [← pow_succ',hx]
    exact (normalizer (K : Set G)).one_mem
end Theory.GroupTheory
