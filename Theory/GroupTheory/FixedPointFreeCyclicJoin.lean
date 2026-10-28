module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Cyclic extensions with a fixed-point-free action

The commutator map of a fixed-point-free automorphism of a finite group is
bijective. Consequently the kernel lies in every overgroup's derived subgroup,
and every element in a nontrivial complement coset has the complement element's
order. For a cyclic complement of order three this gives order three for all
elements outside the kernel. The product cardinality lemma only requires
normalization and a trivial intersection, not ambient normality.

These facts are used for Janko's subgroup `EQ*` in the proof of Lemma 17 of
*A characterization of the Mathieu simple groups, I*, J. Algebra 9 (1968),
pp.16--17. The fixed-point-free commutator map is supplied by Mathlib.
-/

open Subgroup
open scoped Pointwise

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A normalized product with trivial intersection has the product order. -/
public theorem card_sup_of_disjoint_of_normalizes (H K : Subgroup G)
    (hdis : Disjoint H K) (hnorm : K ≤ normalizer (H : Set G)) :
    Nat.card (H ⊔ K : Subgroup G) = Nat.card H * Nat.card K := by
  let f : H × K → (H ⊔ K : Subgroup G) := fun x =>
    ⟨(x.1 : G) * x.2, mul_mem_sup x.1.property x.2.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact mul_injective_of_disjoint hdis (congrArg Subtype.val hab)
    · intro x
      have hx : (x : G) ∈ (H : Set G) * (K : Set G) := by
        rw [← coe_mul_of_right_le_normalizer_left H K hnorm]
        exact x.property
      obtain ⟨a, ha, b, hb, hab⟩ := hx
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm.trans (Nat.card_prod H K)

omit [Finite G] in
private theorem fixedPointFree_normalizer_action (H : Subgroup G) (q : G)
    (hq : q ∈ normalizer (H : Set G))
    (hfree : ∀ h ∈ H, Commute q h → h = 1) :
    MonoidHom.FixedPointFree (H.normalizerMonoidHom ⟨q, hq⟩) := by
  intro h hh
  apply Subtype.ext
  apply hfree h h.property
  exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hh)

/-- Every element of a fixed-point-free coset is conjugate to its representative. -/
public theorem orderOf_mul_of_fixedPointFree (H : Subgroup G) (q : G)
    (hq : q ∈ normalizer (H : Set G))
    (hfree : ∀ h ∈ H, Commute q h → h = 1) (h : G) (hh : h ∈ H) :
    orderOf (h * q) = orderOf q := by
  obtain ⟨a, ha⟩ := (fixedPointFree_normalizer_action H q hq hfree).commutatorMap_surjective
    (⟨h, hh⟩ : H)
  have heq : (a : G) / (q * (a : G) * q⁻¹) = h := congrArg Subtype.val ha
  have hc : h * q = (MulAut.conj (a : G)) q := by
    rw [← heq]
    simp [MulAut.conj_apply, div_eq_mul_inv, mul_assoc]
  rw [hc, MulEquiv.orderOf_eq]

/-- A subgroup admitting a fixed-point-free actor lies in the overgroup derived subgroup. -/
public theorem le_commutator_of_fixedPointFree (H N : Subgroup G) (hHN : H ≤ N)
    (q : G) (hqH : q ∈ normalizer (H : Set G)) (hqN : q ∈ N)
    (hfree : ∀ h ∈ H, Commute q h → h = 1) : H ≤ ⁅N, N⁆ := by
  intro h hh
  obtain ⟨a, ha⟩ := (fixedPointFree_normalizer_action H q hqH hfree).commutatorMap_surjective
    (⟨h, hh⟩ : H)
  have heq : (a : G) / (q * (a : G) * q⁻¹) = h := congrArg Subtype.val ha
  rw [← heq]
  have hc := commutator_mem_commutator (hHN a.property) hqN
  simpa only [commutatorElement_def, div_eq_mul_inv, mul_inv_rev, inv_inv,
    mul_assoc] using hc

omit [Finite G] in
private theorem cyclic_three_fixedPointFree (H : Subgroup G) (q : G)
    (hq3 : orderOf q = 3) (hfree : ∀ h ∈ H, Commute q h → h = 1)
    (a : zpowers q) (ha : a ≠ 1) :
    ∀ h ∈ H, Commute (a : G) h → h = 1 := by
  intro h hh hah
  have hcard : Nat.card (zpowers q) = 3 := by rw [Nat.card_zpowers, hq3]
  have hqa : (⟨q, mem_zpowers q⟩ : zpowers q) ∈ zpowers a :=
    mem_zpowers_of_prime_card hcard ha
  obtain ⟨n, hn⟩ := hqa
  apply hfree h hh
  have hnG : (a : G) ^ n = q := congrArg Subtype.val hn
  rw [← hnG]
  exact hah.zpow_left n

/-- A fixed-point-free cyclic three-extension has order three outside its kernel. -/
public theorem orderOf_outside_cyclic_three_join (H : Subgroup G) (q : G)
    (hqH : q ∈ normalizer (H : Set G)) (hq3 : orderOf q = 3)
    (hfree : ∀ h ∈ H, Commute q h → h = 1)
    (x : G) (hx : x ∈ H ⊔ zpowers q) (hxH : x ∉ H) : orderOf x = 3 := by
  have hQ : zpowers q ≤ normalizer (H : Set G) := zpowers_le.mpr hqH
  have hx' : x ∈ (H : Set G) * (zpowers q : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left H (zpowers q) hQ]
    exact hx
  obtain ⟨h, hh, a, ha, rfl⟩ := hx'
  have ha1 : (⟨a, ha⟩ : zpowers q) ≠ 1 := by
    intro h
    have : a = 1 := congrArg Subtype.val h
    exact hxH (by simpa [this] using hh)
  rw [orderOf_mul_of_fixedPointFree H a (hQ ha)
    (cyclic_three_fixedPointFree H q hq3 hfree ⟨a, ha⟩ ha1) h hh]
  have hd : orderOf a ∣ 3 := hq3 ▸ orderOf_dvd_of_mem_zpowers ha
  exact (Nat.Prime.eq_one_or_self_of_dvd (by decide : Nat.Prime 3) _ hd).resolve_left
    (fun h => ha1 (Subtype.ext (orderOf_eq_one_iff.mp h)))
end Subgroup
