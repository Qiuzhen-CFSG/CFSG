module
public import Theory.GroupTheory.PResidual.PerfectCover
public import Mathlib.GroupTheory.IndexNormal

/-!
# The two-residual of a group of order six

The subgroup of order three has index two and is normal. Its odd-order
 generator belongs to every quotient kernel with two-power index, so this
 subgroup is exactly the two-residual.

This supplies the prime residual order of the marked centralizer quotient
in the elementary-nine row of Aschbacher--Smith 15.1.18(2).
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem card_twoResidual_of_card_six (hc : Nat.card G = 6) :
    Nat.card (pResidual 2 G) = 3 := by
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) 3 (by rw [hc]; decide)
  let K := zpowers g
  have hK : Nat.card K = 3 := by rw [Nat.card_zpowers, hg]
  have hi : K.index = 2 := by
    have hh := K.card_mul_index
    rw [hK, hc] at hh
    omega
  let : K.Normal := normal_of_index_eq_two hi
  have he : pResidual 2 G = K := by
    apply le_antisymm
    · apply sInf_le
      refine ⟨inferInstance, IsPGroup.of_card (n := 1) ?_⟩
      change K.index = 2 ^ 1
      rw [hi]
      rfl
    · apply zpowers_le.mpr
      apply mem_pResidual_of_orderOf_coprime
      rw [hg]
      decide
  rwa [he]
end Subgroup
