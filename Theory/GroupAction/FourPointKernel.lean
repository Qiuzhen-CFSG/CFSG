module
public import Mathlib.Data.Finite.Perm
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# The kernel of an order-27 action on four points

The permutation image has order dividing both 27 and 4!, hence at most
three. The kernel therefore has at least nine elements. This elementary
count is the action-theoretic step in Wong's four-line fixed-set argument
(*On finite groups whose 2-Sylow subgroups have cyclic subgroups of index 2*,
1964, pp.110–111).
-/

namespace MulAction

/-- An order-27 group acting on four points has a kernel of order at least nine. -/
public theorem nine_le_card_ker_toPermHom
    {P X : Type*} [Group P] [Finite P] [Finite X] [MulAction P X]
    (hP : Nat.card P = 27) (hX : Nat.card X = 4) :
    9 ≤ Nat.card (toPermHom P X).ker := by
  let f := toPermHom P X
  have hdiv1 : Nat.card f.range ∣ 27 := hP ▸ Subgroup.card_range_dvd f
  have hdiv2 : Nat.card f.range ∣ 24 := by
    simpa [Nat.card_perm, hX, Nat.factorial] using f.range.card_subgroup_dvd_card
  have hdiv : Nat.card f.range ∣ 3 := Nat.dvd_gcd hdiv1 hdiv2
  have hle : Nat.card f.range ≤ 3 := Nat.le_of_dvd (by decide) hdiv
  have heq : Nat.card f.ker * Nat.card f.range = 27 := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, hP]
  change 9 ≤ Nat.card f.ker
  nlinarith

end MulAction
