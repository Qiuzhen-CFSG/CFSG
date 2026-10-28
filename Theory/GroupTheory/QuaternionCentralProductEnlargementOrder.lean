module

public import Theory.GroupTheory.QuaternionCentralProductIntrinsic
public import Theory.GroupTheory.QuaternionCentralProductSylowIndex

/-!
# The order of a strict local enlargement

A self-centralizing normal quaternion central product bounds the ambient
order by divisibility into 2304. If a proper subgroup of order 192 contains
a Sylow two-subgroup of the ambient group, its index is an odd divisor of
12 different from one, hence three. The ambient group therefore has order
576. The shared Sylow condition is essential to this calculation.

This is the order reduction in Aschbacher–Smith, Lemma 14.2.21, printed
p.988 (PDF p.1005). Recognition of the odd residual as the central product
of two SL₂(3)'s is a separate step; no such recognition is assumed here.
-/

namespace Subgroup

/-- A proper local subgroup of order 192 sharing a Sylow two-subgroup
forces order 576 above a normal self-centralizing quaternion product. -/
public theorem card_eq_576_of_quaternion_product_enlargement
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] (d : QuaternionCentralProductData Q)
    (hcentral : centralizer (Q : Set G) ≤ Q)
    (H : Subgroup G) (hH : Nat.card H = 192) (hproper : H ≠ ⊤)
    (S : Sylow 2 G) (hSH : (S : Subgroup G) ≤ H) : Nat.card G = 576 := by
  have hd := card_dvd_of_selfCentralizing_quaternion_factors Q hcentral d.center_card
    d.left d.right d.left_model d.right_model d.intersection_card d.commute d.span
  have hcount := H.card_mul_index
  rw [hH] at hcount
  rw [← hcount] at hd
  have hindex : H.index ∣ 12 :=
    Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 192) hd
  have hodd : ¬ 2 ∣ H.index :=
    fun h => S.not_dvd_index (h.trans (index_dvd_of_le hSH))
  have hne : H.index ≠ 1 := fun h => hproper (index_eq_one.mp h)
  have hbound : H.index ≤ 12 := Nat.le_of_dvd (by decide) hindex
  have hi : H.index = 3 := by
    interval_cases h : H.index <;> norm_num at *
  rw [hi] at hcount
  exact hcount.symm

end Subgroup
