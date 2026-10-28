module
public import Stellmacher.MaxElementaryOffenderEquality

/-!
# Full maximum families from a small maximum action image

Suppose one maximum elementary subgroup has image of order at most two
on a normal elementary module. If it acts nontrivially, the fixed subgroup
has index at least two. The maximum-elementary cardinal inequality then
forces equality, so the centralizing replacement still has maximum order.
Thus the module centralizer has the full maximum elementary family.
The fixed-core amalgam uses this to discharge the family premise in its
short-block exclusion. Source: Aschbacher–Smith B.2.4(3), pp.75–76.
-/

public noncomputable section
open Subgroup
namespace Stellmacher
open scoped IsMulCommutative
variable {G H : Type*} [Group G] [Finite G] [Group H]

theorem max_family_centralizer_of_small_image
    (S V A : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hVS : V ≤ S) (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (q : G →* H) (hk : q.ker = centralizer (V : Set G))
    (hc : Nat.card (A.map q) ≤ 2) :
    elementaryAbelianMaxSubgroups (S ⊓ centralizer (V : Set G)) ⊆
      elementaryAbelianMaxSubgroups S := by
  let := hA.2.1
  by_cases ha : A ≤ centralizer (V : Set G)
  · exact (maxElementary_centralizer_maxOrder_and_omegaCenter S V A hVS hA
      (le_inf hA.1 ha)).2.1
  have hn : ¬ V ≤ centralizer (A : Set G) := by
    intro hh
    exact ha (le_centralizer_iff.mp hh)
  let F := V ⊓ centralizer (A : Set G)
  have hprod : Nat.card F * F.relIndex V = Nat.card V := by
    simpa only [relIndex_bot_left] using
      relIndex_mul_relIndex (⊥ : Subgroup G) F V bot_le inf_le_left
  have hi : 2 ≤ F.relIndex V := by
    have hpos : 0 < F.relIndex V := by
      have hv : 0 < Nat.card V := Nat.card_pos
      nlinarith
    have hne : F.relIndex V ≠ 1 := by
      intro hh
      exact hn (((relIndex_eq_one.mp hh)).trans inf_le_right)
    omega
  have hb := maxElementary_card_bound_and_eq S V A hVS hA.1 0
    (by simpa using (maxOrder_eq_card_of_mem S A hA).symm) q hk
  have heq : Nat.card V = Nat.card F * Nat.card (A.map q) * 2 ^ 0 := by
    have hlow : Nat.card F * 2 ≤ Nat.card V := by nlinarith
    have hu := hb.1
    change Nat.card V ≤ Nat.card F * Nat.card (A.map q) * 2^0 at hu
    simp only [pow_zero,mul_one] at hu ⊢
    nlinarith
  have hmax := hb.2 heq
  exact (maxElementary_centralizer_maxOrder_and_omegaCenter S V _ hVS hmax
    (le_inf hmax.1 (sup_le (le_centralizer_iff_isMulCommutative.mpr inferInstance)
      inf_le_right))).2.1
end Stellmacher
