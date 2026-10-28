module

public import Theory.SpecificGroups.C4SquareSignSwapInitialEight

/-!
# Elementary subgroup bound in the sign-and-swap group

An elementary subgroup contained in the inverter core has order at most eight.
Otherwise choose an involution outside that core. It commutes with twelve
involutions (including the identity), as checked in the 64-element coordinate
model. The elementary subgroup embeds in that set, and its power-of-two order
is therefore at most eight.

This intrinsic calculation is used for the full binary G₂ Sylow subgroup in
Aschbacher--Smith 14.3.14, printed p.994.
-/

namespace C4SquareSignSwap

private abbrev commutingInvolutions (t : Model) :=
  {x : Model // x ^ 2 = 1 ∧ t * x = x * t}

private theorem commutingInvolutions_card : ∀ t : Model,
    t ^ 2 = 1 → t ∉ inverterCore → Fintype.card (commutingInvolutions t) = 12 := by
  decide +kernel

/-- Every elementary abelian two-subgroup of the full sign-and-swap model
has order at most eight; normality is not required. -/
public theorem elementary_card_le_eight (U : Subgroup Model)
    [IsElementaryAbelian 2 U] : Nat.card U ≤ 8 := by
  by_cases hcore : U ≤ inverterCore
  · by_cases hlarge : 4 < Nat.card U
    · exact (elementary_inverterCore_card_eight_of_gt_four U hlarge hcore).le
    · omega
  obtain ⟨t, ht, htc⟩ := SetLike.not_le_iff_exists.mp hcore
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t ht
  let f : U → commutingInvolutions t := fun u =>
    ⟨u, elemPow_eq_one_of_isElementaryAbelian (u : Model) u.property,
      congrArg Subtype.val ((IsMulCommutative.is_comm (M := U)).comm ⟨t, ht⟩ u)⟩
  have hf : Function.Injective f := by
    intro a b he
    exact Subtype.ext (congrArg (fun x : commutingInvolutions t => x.val) he)
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card (α := commutingInvolutions t),
    commutingInvolutions_card t ht2 htc] at hc
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := U)).mp
    (IsElementaryAbelian.isPGroup 2 U)
  have hpow : 2 ^ n < 2 ^ 4 := by omega
  have hn4 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hpow
  rw [hn]
  exact Nat.pow_le_pow_right (by decide) (by omega : n ≤ 3)

end C4SquareSignSwap
