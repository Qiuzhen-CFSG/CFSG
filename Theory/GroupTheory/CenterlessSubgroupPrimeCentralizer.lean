module
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Prime elements centralizing centerless subgroups

A subgroup with trivial center is disjoint from any subgroup centralizing
it. If its order is divisible by p, a commuting element of order p therefore
forces p² to divide the ambient order, by the order of their subgroup product.
This is the elementary order obstruction used in the J₂ row of
Aschbacher--Smith 4.3.16, printed p.618.
-/

public section
noncomputable section
open Subgroup
namespace Subgroup
variable {A : Type*} [Group A]

/-- A single p-factor in the ambient order excludes a commuting element of order p. -/
theorem no_prime_centralizer_of_square_free_order
    (X : Subgroup A) (hz : center X = ⊥) {p : ℕ}
    (hd : p ∣ Nat.card X) (hnot : ¬p*p ∣ Nat.card A)
    (a : A) (ha : a ∈ centralizer (X : Set A)) (ho : orderOf a = p) : False := by
  let Z := zpowers a
  have hZX : Z ≤ centralizer (X : Set A) := zpowers_le.mpr ha
  have hdis : Disjoint X Z := by
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro x hx
    have hxc : (⟨x,hx.1⟩ : X) ∈ center X := mem_center_iff.mpr fun y =>
      Subtype.ext (hZX hx.2 y y.property)
    rw [hz,mem_bot] at hxc
    exact mem_bot.mpr (congrArg Subtype.val hxc)
  have he := card_sup_eq_mul_of_normalizes_of_disjoint X Z
    (hZX.trans (centralizer_le_normalizer _)) hdis
  have hc : Nat.card Z = p := by rw [Nat.card_zpowers,ho]
  have hd' : p*p ∣ Nat.card (X ⊔ Z : Subgroup A) := by
    rw [he,hc]
    exact Nat.mul_dvd_mul hd dvd_rfl
  exact hnot (hd'.trans (X ⊔ Z).card_subgroup_dvd_card)
end Subgroup
