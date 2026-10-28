module

public import GorensteinWalter.Section4.PSL2ReflectedTorusCard
public import Theory.GroupTheory.SelfCentralizingCore
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# Parameters forced by odd PSL₂ involution centralizers

An involution centralizer has a cyclic normal torus of order `(q ± 1) / 2`.
If its odd core is trivial, that normal nilpotent torus is a two-group.
Consequently one of `q - 1` and `q + 1` is a power of two. The automorphism
version retains the full fixed subgroup of the actual inner involution.

Source: Aschbacher--Smith, proof of 1.1.5(3), printed p.503; the imported
reflected-torus calculation is Huppert II.8.3--4.
-/

public section
open Subgroup Theory.GroupTheory GorensteinWalter
open scoped MatrixGroups

namespace Theory.PSL2

/-- Trivial odd core in an involution centralizer forces an adjacent two-power. -/
theorem adjacent_two_power_of_involution_centralizer_oddCore_eq_bot {K : Type*} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    {t : PSL(2,K)} (ht : orderOf t = 2)
    (hc : pPrimeCore 2 (centralizer ({t} : Set PSL(2,K))) = ⊥) :
    ∃ n : ℕ, Nat.card K - 1 = 2 ^ n ∨ Nat.card K + 1 = 2 ^ n := by
  have htI : IsInvolution t := ⟨by intro h; simp [h] at ht,
    by simpa only [ht] using pow_orderOf_eq_one t⟩
  obtain ⟨T, s, hT, _, hs, _, hinv, hC, _, hcard⟩ :=
    psl2_reflected_torus_card hK htI
  let C := centralizer ({t} : Set PSL(2,K))
  have hTC : T ≤ C := by rw [show C = T ⊔ zpowers s from hC]; exact le_sup_left
  have hsN : s ∈ normalizer (T : Set PSL(2,K)) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hinv x hx]
      exact T.inv_mem hx
    · intro hx
      have hx' := T.inv_mem hx
      have he : s * (s * x * s⁻¹) * s⁻¹ = x := by
        calc
          _ = (s * s) * x * (s * s)⁻¹ := by group
          _ = x := by rw [← pow_two, hs.2]; simp
      rwa [← hinv _ hx, he] at hx'
  have hTN : (T.subgroupOf C).Normal :=
    (normal_subgroupOf_iff_le_normalizer hTC).mpr (by
      rw [show C = T ⊔ zpowers s from hC]
      exact sup_le T.le_normalizer (zpowers_le.mpr hsN))
  let : IsCyclic T := hT
  let : IsCyclic (T.subgroupOf C) := isCyclic_of_injective
    (subgroupOfEquivOfLe hTC).toMonoidHom (subgroupOfEquivOfLe hTC).injective
  let : CommGroup (T.subgroupOf C) := IsCyclic.commGroup
  have hp := isPGroup_of_nilpotent_normal (p := 2) (T.subgroupOf C) hTN
    inferInstance hc
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hTcard : Nat.card T = 2 ^ n :=
    (Nat.card_congr (subgroupOfEquivOfLe hTC).toEquiv).symm.trans hn
  have ho : Odd (Nat.card K) := by
    obtain ⟨p, f, _, ho, _, he⟩ := hK
    rw [he]
    exact ho.pow
  obtain ⟨k, hk⟩ := ho
  refine ⟨n + 1, ?_⟩
  rw [pow_succ, ← hTcard]
  rcases hcard with hm | hp
  · left; omega
  · right; omega

/-- The same parameter obstruction for the literal full fixed group of an
inner involutory automorphism. -/
theorem adjacent_two_power_of_inner_fixed_oddCore_eq_bot
    {K : Type*} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (a : MulAut PSL(2,K))
    (ha : orderOf a = 2) (hi : ∃ x, a = MulAut.conj x)
    (hc : pPrimeCore 2 a.fixedSubgroup = ⊥) :
    ∃ n : ℕ, Nat.card K - 1 = 2 ^ n ∨ Nat.card K + 1 = 2 ^ n := by
  obtain ⟨x, hx, _, he⟩ :=
    MulAut.inner_involution_representative (psl2_center_eq_bot K) a ha hi
  rw [he] at hc
  exact adjacent_two_power_of_involution_centralizer_oddCore_eq_bot hK hx hc

end Theory.PSL2
