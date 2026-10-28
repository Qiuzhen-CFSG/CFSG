module
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.PGroup

/-!
# A normal cubic supplement through a quotient

A normal subgroup of order three intersects a two-subgroup trivially. Their
product has relative index three, and a surjective preimage preserves that
index when its kernel is contained in the original two-subgroup.
-/

public section
open Subgroup
namespace Subgroup
variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]

omit [Finite G] in
/-- Lifting the product of a normal cubic subgroup and a two-subgroup
preserves its index when the kernel is already in the two-subgroup. -/
theorem normal_cubic_preimage_relIndex (q : G →* Q) (hq : Function.Surjective q)
    (R : Subgroup G) (hR : IsPGroup 2 R) (hk : q.ker ≤ R)
    (C : Subgroup Q) [C.Normal] (hC : Nat.card C = 3) :
    R.relIndex ((C ⊔ R.map q).comap q) = 3 := by
  have hp : IsPGroup 3 C := IsPGroup.of_card (n := 1) (by simpa using hC)
  have hd : Disjoint C (R.map q) := hp.disjoint_of_coprime (hR.map q) (by decide)
  have hc := card_sup_eq_mul_of_normalizes_of_disjoint C (R.map q)
    le_normalizer_of_normal hd
  rw [hC] at hc
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup Q) (R.map q)
    (C ⊔ R.map q) bot_le le_sup_right
  simp only [relIndex_bot_left] at hcount
  have hi : (R.map q).relIndex (C ⊔ R.map q) = 3 := by
    rw [hc, Nat.mul_comm 3] at hcount
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hcount
  have he := relIndex_map_map q R ((C ⊔ R.map q).comap q)
  rw [map_comap_eq_self_of_surjective hq, sup_eq_left.mpr hk,
    sup_eq_left.mpr (show q.ker ≤ (C ⊔ R.map q).comap q from
      fun x hx => by change q x ∈ C ⊔ R.map q; rw [hx]; exact one_mem _)] at he
  exact he.symm.trans hi
end Subgroup
