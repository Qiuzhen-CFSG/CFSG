module

public import Theory.GroupTheory.CentricRadicalAutomorphisms
public import Theory.SpecificGroups.ReeTwo.Sylow
public import Mathlib.GroupTheory.IndexNormal

import Mathlib.Tactic.NormNum

/-!
# Order reduction for large Ree two centric radical candidates

A subgroup of the verified order-4096 Sylow model with order at least 1024
is either the whole group or has order 2048 or 1024. In the former proper
case it is normal. If it is also centric and its normalizer action intersects
the automorphism two-core only in inner automorphisms, its automorphism group
cannot be a two-group.

These are necessary conditions, not an assertion that the candidate list is
exhaustive. The remaining classification requires the automorphism analysis
of the subgroups of orders 2048 and 1024, including those inside the parity
kernel.

Source: the order is proved from Shinoda (1975), (2.1)–(2.3), in `Sylow`.
The candidate problem is motivated by van Beek (2024), Proposition 3.1, p. 10;
the reductions here use Lagrange's theorem and the p-group normalizer condition.
-/

namespace ReeTwo.SylowModel

/-- The only possible orders of a proper subgroup of order at least 1024. -/
public theorem large_subgroup_cases (U : Subgroup SylowModel)
    (hU : 1024 ≤ Nat.card U) :
    U = ⊤ ∨ Nat.card U = 2048 ∨ Nat.card U = 1024 := by
  have hd : Nat.card U ∣ 2 ^ 12 := by
    norm_num only [Nat.reducePow]
    rw [← card]
    exact U.card_subgroup_dvd_card
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp hd
  have hk10 : 10 ≤ k := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    calc
      2 ^ 10 = 1024 := by norm_num
      _ ≤ Nat.card U := hU
      _ = 2 ^ k := he
  have hk' : k = 10 ∨ k = 11 ∨ k = 12 := by omega
  rcases hk' with rfl | rfl | rfl
  · exact Or.inr (Or.inr (by norm_num only [Nat.reducePow] at he; exact he))
  · exact Or.inr (Or.inl (by norm_num only [Nat.reducePow] at he; exact he))
  · apply Or.inl
    apply U.eq_top_of_card_eq
    rw [card, he]
    norm_num

/-- The order-2048 case is exactly the index-two case. -/
public theorem index_eq_two_of_card_eq_2048 (U : Subgroup SylowModel)
    (hU : Nat.card U = 2048) : U.index = 2 := by
  have hi := U.index_mul_card
  rw [hU, card] at hi
  omega

/-- Every order-2048 subgroup of the model is normal. -/
public theorem normal_of_card_eq_2048 (U : Subgroup SylowModel)
    (hU : Nat.card U = 2048) : U.Normal :=
  U.normal_of_index_eq_two (index_eq_two_of_card_eq_2048 U hU)

/-- A proper intrinsic centric radical candidate cannot have a two-group
as its entire automorphism group. -/
public theorem eq_top_of_centric_radical_of_isPGroup_mulAut
    (U : Subgroup SylowModel)
    (hc : Subgroup.centralizer (U : Set SylowModel) ≤ U)
    (hr : U.normalizerMonoidHom.range ⊓ pCore 2 (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range)
    (ha : IsPGroup 2 (MulAut U)) : U = ⊤ := by
  have hS : IsPGroup 2 SylowModel := IsPGroup.of_card (n := 12) card
  let : Group.IsNilpotent SylowModel := hS.isNilpotent
  exact Subgroup.eq_top_of_centric_radical_of_isPGroup_mulAut
    Group.normalizerCondition_of_isNilpotent U hc 2 hr ha

/-- Necessary order and automorphism conditions for a large proper candidate.
No condition excluding the parity kernel is imposed. -/
public theorem large_centric_radical_cases (U : Subgroup SylowModel)
    (hc : Subgroup.centralizer (U : Set SylowModel) ≤ U)
    (hr : U.normalizerMonoidHom.range ⊓ pCore 2 (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range)
    (hU : 1024 ≤ Nat.card U) :
    U = ⊤ ∨ ((Nat.card U = 2048 ∨ Nat.card U = 1024) ∧
      ¬ IsPGroup 2 (MulAut U)) := by
  by_cases ht : U = ⊤
  · exact Or.inl ht
  · refine Or.inr ⟨(large_subgroup_cases U hU).resolve_left ht, ?_⟩
    exact fun ha => ht (eq_top_of_centric_radical_of_isPGroup_mulAut U hc hr ha)

end ReeTwo.SylowModel
