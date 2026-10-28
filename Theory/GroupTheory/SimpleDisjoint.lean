module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Coset.Card

/-!
# A simple subgroup normalizing a subgroup of incompatible order

If a simple subgroup `K` normalizes `L`, then `K ∩ L` is normal in `K`.
It is therefore trivial unless `K ≤ L`. A failure of order divisibility
excludes the latter case. This is useful when a local factor has restricted
prime divisors.
-/

@[expose] public section
namespace Subgroup

/-- Simplicity and normalization turn an order obstruction into disjointness. -/
theorem disjoint_of_simple_of_normalizes_of_not_card_dvd
    {G : Type*} [Group G] (K L : Subgroup G) [IsSimpleGroup K]
    (hn : K ≤ normalizer (L : Set G)) (hc : ¬ Nat.card K ∣ Nat.card L) : Disjoint L K := by
  let : (L.subgroupOf K).Normal := ⟨fun x hx g => (hn g.property (x : G)).mp hx⟩
  rcases (inferInstance : (L.subgroupOf K).Normal).eq_bot_or_eq_top with heq | heq
  · apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro x hx
    have hh : (⟨x, hx.2⟩ : K) ∈ L.subgroupOf K := hx.1
    rw [heq] at hh
    exact congrArg Subtype.val hh
  · apply False.elim
    apply hc
    apply card_dvd_of_le
    intro x hx
    have hh : (⟨x, hx⟩ : K) ∈ L.subgroupOf K := by rw [heq]; trivial
    exact hh

end Subgroup
