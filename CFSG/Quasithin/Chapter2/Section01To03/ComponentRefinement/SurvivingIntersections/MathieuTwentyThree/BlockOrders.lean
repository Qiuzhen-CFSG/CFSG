module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.BlockObstructions

/-!
# The A7 quotient excludes all chi-zero block types

The actual quotient of a chi-zero block has order 3, 60, or
2^n(2^(2n)-1), with n at least two. None of these orders is 2520.
This elementary obstruction applies after the subnormal-group argument has
identified a quotient with A7; it does not identify that quotient by itself.

Source: Aschbacher–Smith C.1.12 and 2.3.9(7)(f), printed pp.124 and 525–526.
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement

open Subgroup ChapterC

/-- An actual A7-sized quotient by the two-core cannot be a chi-zero block. -/
theorem not_chiZero_of_quotient_card_2520 {K : Type*} [Group K]
    (hq : Nat.card (K ⧸ pCore 2 K) = 2520) : ¬ IsChiZeroBlock K := by
  intro h
  rcases LieType.chiZero_order_module h with ⟨n, hn, he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩
  · have hn4 : n < 4 := by
      by_contra hn4
      have hl : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
      have hr : 2 ^ 8 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by decide) (by omega)
      have hp := Nat.mul_le_mul hl (Nat.sub_le_sub_right hr 1)
      rw [← he, hq] at hp
      norm_num at hp
    interval_cases n <;> norm_num [hq] at he
  · omega
  · omega

end CFSG.Quasithin.Chapter2.ComponentRefinement

end
