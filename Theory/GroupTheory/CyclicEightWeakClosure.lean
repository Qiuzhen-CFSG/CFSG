module

public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Theory.GroupTheory.NormalizedSupCard
import Mathlib.Tactic.Group

/-!
# Weak closure of a central cyclic subgroup of order eight

A cyclic subgroup K of order 8, central in a subgroup P of order 32, is
weakly closed in P when the centralizer of its involution normalizes K.
Any conjugate inside P meets K nontrivially by the product-order formula.
The common involution is unique in both cyclic two-groups, so the
conjugating element centralizes it and hence normalizes K.

This is the weak-closure step of Suzuki (1965), Section II, Lemma 3.
-/

namespace Subgroup

/-- The order 8 intersection argument for weak closure in order 32. -/
public theorem weaklyClosed_cyclic_eight_of_involution_centralizer
    {G : Type*} [Group G] [Finite G]
    (P K : Subgroup G) [IsCyclic K]
    (hP : Nat.card P = 32) (hK : Nat.card K = 8) (hKP : K ≤ P)
    (hcentral : P ≤ centralizer (K : Set G))
    (j : K) (hj : orderOf j = 2)
    (hcent : centralizer ({(j : G)} : Set G) ≤ normalizer (K : Set G)) :
    K ≤ P ∧ ∀ x : G, K.map (MulAut.conj x⁻¹).toMonoidHom ≤ P →
      K.map (MulAut.conj x⁻¹).toMonoidHom = K := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hKP, ?_⟩
  intro x hx
  let R := K.map (MulAut.conj x⁻¹).toMonoidHom
  change R ≤ P at hx
  have hRcard : Nat.card R = 8 :=
    (card_map_of_injective (MulAut.conj x⁻¹).injective).trans hK
  have hnorm : R ≤ normalizer (K : Set G) :=
    hx.trans (hcentral.trans (centralizer_le_normalizer (K : Set G)))
  have hmeet : K ⊓ R ≠ ⊥ := by
    intro he
    have hm := card_mul_eq_card_inf_mul_card_sup_of_normalizes K R hnorm
    rw [hK, hRcard, he, card_bot, one_mul] at hm
    have hb := card_le_of_le (sup_le hKP hx)
    rw [hP, ← hm] at hb
    norm_num at hb
  have hRK : R.subgroupOf K ≠ ⊥ := by
    intro he
    apply hmeet
    apply bot_unique
    intro z hz
    have hz' : (⟨z, hz.1⟩ : K) ∈ R.subgroupOf K := hz.2
    rw [he, mem_bot] at hz'
    exact congrArg Subtype.val hz'
  have hjR : (j : G) ∈ R :=
    (IsPGroup.of_card (n := 3) hK).involution_mem_subgroup_of_ne_bot hj _ hRK
  let e := K.equivMapOfInjective (MulAut.conj x⁻¹).toMonoidHom
    (MulAut.conj x⁻¹).injective
  let : IsCyclic R := e.isCyclic.mp inferInstance
  have hxeq : e j = (⟨(j : G), hjR⟩ : R) :=
    IsCyclic.eq_of_orderOf_eq_two ((e.orderOf_eq j).trans hj) (by
      calc
        orderOf (⟨(j : G), hjR⟩ : R) = orderOf (j : G) := (orderOf_coe _).symm
        _ = orderOf j := orderOf_coe j
        _ = 2 := hj)
  have heG : x⁻¹ * (j : G) * x = (j : G) := by
    have he := congrArg Subtype.val hxeq
    change x⁻¹ * (j : G) * (x⁻¹)⁻¹ = (j : G) at he
    simpa only [inv_inv] using he
  have hxcent : x⁻¹ ∈ centralizer ({(j : G)} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    calc
      x⁻¹ * (j : G) = (x⁻¹ * (j : G) * x) * x⁻¹ := by group
      _ = (j : G) * x⁻¹ := by rw [heG]
  exact mem_normalizer_iff_map_conj_eq.mp (hcent hxcent)

end Subgroup
