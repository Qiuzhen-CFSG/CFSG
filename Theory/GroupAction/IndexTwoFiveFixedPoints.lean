module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.IndexNormal

/-!
# Five-fixed elements outside an index-two subgroup

Let a group of order five act on a finite group `Q`. Suppose `R` is a
normal subgroup of index two, at most two fixed elements lie in `R`, and
the order of `Q` is congruent to four modulo five. The fixed subgroup has
order four and contains an element outside `R`. That element has fourth
power one.

The index-two condition bounds the fixed subgroup by four. Orbit counting
modulo five then gives its exact order. This is the finite-action step for
the proper residual extension in Stellmacher (10.1)(b): the local core
has order 1024, the residual has order 512, and the residual fixed subgroup
is its center of order two. No ambient fusion statement is used here.
-/

namespace Theory.GroupAction

public theorem fixed_card_four_of_index_two
    {A Q : Type*} [Group A] [Finite A] [Group Q] [Finite Q]
    [MulDistribMulAction A Q]
    (R : Subgroup Q) [R.Normal] (hA : Nat.card A = 5)
    (hindex : R.index = 2) (hQ : Nat.card Q % 5 = 4)
    (hfixed : Nat.card ((FixedPoints.subgroup A Q).subgroupOf R) ≤ 2) :
    Nat.card (FixedPoints.subgroup A Q) = 4 := by
  let F := FixedPoints.subgroup A Q
  have hswap : Nat.card (R.subgroupOf F) = Nat.card (F.subgroupOf R) := by
    apply Nat.card_congr
    exact {
      toFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      invFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hi : (R.subgroupOf F).index ≤ 2 := by
    apply Nat.le_of_dvd (by decide : 0 < 2)
    exact hindex ▸ R.relIndex_dvd_index_of_normal F
  have hcount := (R.subgroupOf F).index_mul_card
  rw [hswap] at hcount
  change (R.subgroupOf F).index * Nat.card ((FixedPoints.subgroup A Q).subgroupOf R) =
    Nat.card F at hcount
  have hbound : Nat.card F ≤ 4 := by
    have := Nat.mul_le_mul hi hfixed
    omega
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hfive : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hm := hfive.card_modEq_card_fixedPoints Q
  change Nat.card Q % 5 = Nat.card F % 5 at hm
  change Nat.card F = 4
  omega

public theorem exists_fixed_pow_four_not_mem_of_index_two
    {A Q : Type*} [Group A] [Finite A] [Group Q] [Finite Q]
    [MulDistribMulAction A Q]
    (R : Subgroup Q) [R.Normal] (hA : Nat.card A = 5)
    (hindex : R.index = 2) (hQ : Nat.card Q % 5 = 4)
    (hfixed : Nat.card ((FixedPoints.subgroup A Q).subgroupOf R) ≤ 2) :
    ∃ x : Q, x ∈ FixedPoints.subgroup A Q ∧ x ∉ R ∧ x ^ 4 = 1 := by
  have hcard := fixed_card_four_of_index_two R hA hindex hQ hfixed
  have hnot : ¬ FixedPoints.subgroup A Q ≤ R := by
    intro hle
    have hc := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [hc, hcard] at hfixed
    omega
  obtain ⟨x, hx, hxR⟩ : ∃ x : Q, x ∈ FixedPoints.subgroup A Q ∧ x ∉ R := by
    simpa only [SetLike.le_def, not_forall, exists_prop] using hnot
  refine ⟨x, hx, hxR, ?_⟩
  have hp : (⟨x, hx⟩ : FixedPoints.subgroup A Q) ^ 4 = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  exact congrArg Subtype.val hp

end Theory.GroupAction
