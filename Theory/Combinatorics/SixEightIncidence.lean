module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic

/-!
# Reciprocal incidence between six and eight points

A relation with six uniform rows of size zero or four and eight columns of
size one or three must have every row of size four and every column of size
three. The proof counts the same literal incident pairs in both directions.
-/

public section
namespace FiniteIncidence
variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The small incidence balance needed for the point-core geometry of an
original HS elementary sixteen. -/
theorem six_eight_degrees (R : X → Y → Prop) [DecidableRel R]
    (hX : Fintype.card X = 6) (hY : Fintype.card Y = 8)
    (hrow : ∀ x, Fintype.card {y // R x y} = 0 ∨ Fintype.card {y // R x y} = 4)
    (hcol : ∀ y, Fintype.card {x // R x y} = 1 ∨ Fintype.card {x // R x y} = 3)
    (huniform : ∀ x x', Fintype.card {y // R x y} = Fintype.card {y // R x' y}) :
    (∀ x, Fintype.card {y // R x y} = 4) ∧
      (∀ y, Fintype.card {x // R x y} = 3) := by
  classical
  let row (x : X) := Fintype.card {y // R x y}
  let col (y : Y) := Fintype.card {x // R x y}
  have balance : ∑ x, row x = ∑ y, col y := by
    simp only [row, col, Fintype.card_subtype, Finset.card_filter]
    exact Finset.sum_comm
  have hypos : 0 < Fintype.card Y := by omega
  let y₀ : Y := Classical.choice (Fintype.card_pos_iff.mp hypos)
  have hr4 : ∀ x, row x = 4 := by
    intro x
    rcases hrow x with hz | h4
    · have hzall : ∀ t, row t = 0 := fun t => (huniform t x).trans hz
      have hs : ∑ t, row t = 0 := by simp only [hzall, Finset.sum_const_zero]
      have hle : col y₀ ≤ ∑ y, col y := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
      rw [← balance, hs] at hle
      rcases hcol y₀ with h1 | h3 <;> change col y₀ = _ at * <;> omega
    · exact h4
  have hsum : ∑ y, col y = 24 := by
    rw [← balance]
    simp only [hr4, Finset.sum_const, Finset.card_univ, hX, smul_eq_mul]
  have hcle : ∀ y, col y ≤ 3 := by
    intro y
    rcases hcol y with h1 | h3
    · change col y = 1 at h1; omega
    · change col y = 3 at h3; omega
  have hcols : ∀ y, col y = 3 := by
    intro y
    by_contra hn
    have hlt : col y < 3 := lt_of_le_of_ne (hcle y) hn
    have hs : (∑ t, col t) < ∑ _ : Y, 3 := by
      apply Finset.sum_lt_sum
      · intro t _; exact hcle t
      · exact ⟨y, Finset.mem_univ y, hlt⟩
    simp only [Finset.sum_const, Finset.card_univ, hY, smul_eq_mul] at hs
    omega
  exact ⟨hr4, hcols⟩

end FiniteIncidence
