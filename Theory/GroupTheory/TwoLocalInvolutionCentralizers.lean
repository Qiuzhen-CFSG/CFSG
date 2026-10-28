module

public import Theory.Quasithin
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Two-local cores when involution centralizers are two-groups

Suppose every involution centralizer in a finite group is a two-group.
For a nonidentity normal two-subgroup Q, choose an involution t in Q.
Then C(Q) lies in C(t), so C(Q) is itself a normal two-subgroup. Both Q
and C(Q) lie in O₂, which implies that O₂ is self-centralizing.

Apply this argument inside N(Q), using the relative normality of Q there.
This supplies the small alternating cases of Aschbacher–Smith,
*The Classification of Quasithin Groups*, Theorem 0.1.2(3), printed p.4.
-/

namespace Theory.GroupTheory

open Subgroup

/-- A nonidentity normal two-subgroup and two-group involution centralizers
force the actual two-core to be self-centralizing. -/
public theorem centralizer_pCore_le_of_involution_centralizers
    {G : Type*} [Group G] [Finite G]
    (hc : ∀ x : G, orderOf x = 2 → IsPGroup 2 (centralizer ({x} : Set G)))
    (Q : Subgroup G) [Q.Normal] (hp : IsPGroup 2 Q) (hne : Q ≠ ⊥) :
    centralizer (pCore 2 G : Set G) ≤ pCore 2 G := by
  have hcard : 2 ∣ Nat.card Q := hp.card_eq_or_dvd.resolve_left (by
    exact (Q.one_lt_card_iff_ne_bot.mpr hne).ne')
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 hcard
  have hct : IsPGroup 2 (centralizer ({(t : G)} : Set G)) :=
    hc t ((Subgroup.orderOf_coe t).trans ht)
  have hCQ : IsPGroup 2 (centralizer (Q : Set G)) :=
    hct.to_le (centralizer_le (Set.singleton_subset_iff.mpr t.property))
  have hQcore : Q ≤ pCore 2 G := le_sSup ⟨inferInstance, hp⟩
  have hCcore : centralizer (Q : Set G) ≤ pCore 2 G := le_sSup ⟨inferInstance, hCQ⟩
  exact (centralizer_le hQcore).trans hCcore

/-- The criterion applies to every two-local, with normality inside that local. -/
public theorem twoLocal_centralizer_pCore_le_of_involution_centralizers
    {G : Type*} [Group G] [Finite G]
    (hc : ∀ x : G, orderOf x = 2 → IsPGroup 2 (centralizer ({x} : Set G)))
    (M : Subgroup G) (hM : IsTwoLocal M) :
    centralizer (pCore 2 M : Set M) ≤ pCore 2 M := by
  obtain ⟨Q, hne, hp, rfl⟩ := hM
  have hcN : ∀ x : normalizer (Q : Set G), orderOf x = 2 →
      IsPGroup 2 (centralizer ({x} : Set (normalizer (Q : Set G)))) := by
    intro x hx
    have h := hc x ((Subgroup.orderOf_coe x).trans hx)
    have heq : centralizer ({x} : Set (normalizer (Q : Set G))) =
        (centralizer ({(x : G)} : Set G)).comap (normalizer (Q : Set G)).subtype := by
      ext y
      simp only [mem_centralizer_singleton_iff, mem_comap, Subtype.ext_iff]
      rfl
    rw [heq]
    exact h.comap_of_injective _ Subtype.val_injective
  apply centralizer_pCore_le_of_involution_centralizers hcN
    (Q.subgroupOf (normalizer Q)) hp.comap_subtype
  have hQ : Nontrivial Q := Q.nontrivial_iff_ne_bot.mpr hne
  exact (Q.subgroupOf (normalizer Q)).nontrivial_iff_ne_bot.mp
    (Subgroup.subgroupOfEquivOfLe (le_normalizer (H := Q))).nontrivial

end Theory.GroupTheory
