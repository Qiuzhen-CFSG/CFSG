module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Prime-order centralizers and local p-cores

Suppose every element of order p has a p-group centralizer. If M normalizes
a nonidentity p-subgroup Q contained in M, then its p-core is self-centralizing.
Indeed Q lies in the p-core. Choose an element z of order p in Q; the centralizer
of the p-core embeds into C_G(z), so it is itself a normal p-subgroup of M.

This criterion supplies the characteristic-two calculation for the PSL₂
Fermat–Mersenne examples in Aschbacher–Smith, Theorem 0.1.2(4), printed p.4.
Normality here is relative to M, not to the ambient group.
-/

open Subgroup

/-- A normalized nonidentity p-subgroup has a characteristic-p overgroup when
all ambient prime-order centralizers are p-groups. -/
public theorem centralizer_pCore_le_of_prime_order_centralizers
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hc : ∀ z : G, orderOf z = p → IsPGroup p (centralizer ({z} : Set G)))
    (Q M : Subgroup G) (hQ : IsPGroup p Q) (hQne : Q ≠ ⊥)
    (hQM : Q ≤ M) (hMN : M ≤ normalizer (Q : Set G)) :
    centralizer (pCore p M : Set M) ≤ pCore p M := by
  have hn : (Q.subgroupOf M).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQM).mpr hMN
  have hQcore : Q.subgroupOf M ≤ pCore p M := le_sSup ⟨hn, hQ.comap_subtype⟩
  have hpd : p ∣ Nat.card Q := hQ.card_eq_or_dvd.resolve_left
    (fun h => hQne ((Subgroup.card_eq_one).mp h))
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Q) p hpd
  have hzg : orderOf (z : G) = p := (Subgroup.orderOf_coe z).trans hz
  let C := centralizer (pCore p M : Set M)
  have hmap : C.map M.subtype ≤ centralizer ({(z : G)} : Set G) := by
    rintro x ⟨y, hy, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    exact (congrArg Subtype.val (hy ⟨z, hQM z.property⟩ (hQcore z.property))).symm
  have hpC : IsPGroup p C := by
    exact ((hc z hzg).to_le hmap).of_equiv
      (Subgroup.equivMapOfInjective C M.subtype M.subtype_injective).symm
  exact le_sSup ⟨inferInstance, hpC⟩
