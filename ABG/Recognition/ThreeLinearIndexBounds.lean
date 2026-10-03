module

public import Theory.GroupAction.SimpleCosets
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.IntervalCases

/-!
# The index alternatives in Wong's linear branch

In a simple group of order 5616 a proper subgroup containing subgroups of
orders 36 and 48 has index 13 or 39. The two subgroup orders force its index
to divide 39. Index one is excluded by properness and index three by the
faithful coset action of a simple group.

Source: Wong (1964), Theorem 6(b), p.110. Excluding index 39 requires the
additional structure of the involution centralizer.
-/

namespace ABG

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- Simplicity excludes index three in the order-5616 branch. -/
public theorem index_ne_three_of_order_5616 (hG : Nat.card G = 5616)
    (K : Subgroup G) : K.index ≠ 3 := by
  intro hK
  have hproper : K ≠ ⊤ := by
    intro h
    simp [h] at hK
  have hd := K.card_dvd_factorial_index_of_simple hproper
  norm_num [hG, hK, Nat.factorial] at hd

/-- Wong's generated subgroup has only two remaining possible indices. -/
public theorem index_thirteen_or_thirtynine_of_subgroup_orders
    (hG : Nat.card G = 5616) (M C K : Subgroup G)
    (hM : Nat.card M = 36) (hC : Nat.card C = 48)
    (hMK : M ≤ K) (hCK : C ≤ K) (hK : K ≠ ⊤) :
    K.index = 13 ∨ K.index = 39 := by
  have hMi : M.index = 156 := by
    have h := M.card_mul_index
    rw [hM, hG] at h
    omega
  have hCi : C.index = 117 := by
    have h := C.card_mul_index
    rw [hC, hG] at h
    omega
  have hdM : K.index ∣ 156 := hMi ▸ Subgroup.index_dvd_of_le hMK
  have hdC : K.index ∣ 117 := hCi ▸ Subgroup.index_dvd_of_le hCK
  have hd : K.index ∣ 39 := by simpa using Nat.dvd_gcd hdM hdC
  have hle : K.index ≤ 39 := Nat.le_of_dvd (by decide) hd
  have hne1 : K.index ≠ 1 := fun h => hK (Subgroup.index_eq_one.mp h)
  have hne3 := index_ne_three_of_order_5616 hG K
  interval_cases h : K.index <;> norm_num at *

end ABG
