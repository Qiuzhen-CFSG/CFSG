module
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Tactic

/-!
# Products in three-step strictly triangular matrix rings

Three strictly block-lower matrices for a three-block flag have zero product.
Consequently commutation with a product of unipotent factors reduces to a
linear sum of commutators whenever the relevant triple products vanish.
-/

public section
open scoped BigOperators
namespace Theory.LinearAlgebra.ThreeBlockProduct

 theorem triple_zero {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Ring R] (b : n → Fin 3) (A B C : Matrix n n R)
    (hA : ∀ i j, b i ≤ b j → A i j = 0)
    (hB : ∀ i j, b i ≤ b j → B i j = 0)
    (hC : ∀ i j, b i ≤ b j → C i j = 0) : A * B * C = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro l _
  by_cases h1 : b i ≤ b l
  · rw [hA i l h1, zero_mul, zero_mul]
  by_cases h2 : b l ≤ b k
  · rw [hB l k h2, mul_zero, zero_mul]
  have h3 : b k ≤ b j := by
    have hi := (b i).isLt
    have hj := (b j).isLt
    have hk := (b k).isLt
    have hl := (b l).isLt
    simp only [Fin.le_iff_val_le_val] at *
    omega
  rw [hC k j h3, mul_zero]

 theorem prod_mul {R : Type*} [Ring R] (L : List R) (z : R)
    (h : ∀ a ∈ L, ∀ b ∈ L, a * b * z = 0) :
    (L.map (1 + ·)).prod * z = z + (L.map (· * z)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have hL := ih (fun x hx y hy => h x (by simp [hx]) y (by simp [hy]))
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [mul_assoc, hL, add_mul, one_mul, mul_add]
    have hz : a * (L.map (· * z)).sum = 0 := by
      rw [← List.sum_map_mul_left]
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      exact (mul_assoc a b z).symm.trans (h a (by simp) b (by simp [hb]))
    rw [hz, add_zero]
    abel

 theorem mul_prod {R : Type*} [Ring R] (L : List R) (z : R)
    (h : ∀ a ∈ L, ∀ b ∈ L, z * a * b = 0) :
    z * (L.map (1 + ·)).prod = z + (L.map (z * ·)).sum := by
  induction L using List.reverseRecOn with
  | nil => simp
  | append_singleton L a ih =>
    have hL := ih (fun x hx y hy => h x (by simp [hx]) y (by simp [hy]))
    simp only [List.map_append, List.map_singleton, List.prod_append,
      List.prod_singleton, List.sum_append, List.sum_singleton]
    rw [← mul_assoc, hL, mul_add, mul_one, add_mul]
    have hz : (L.map (z * ·)).sum * a = 0 := by
      rw [← List.sum_map_mul_right]
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      exact h b (by simp [hb]) a (by simp)
    rw [hz, add_zero]
    abel

 theorem prod_commutation {R : Type*} [Ring R] (L : List R) (z : R)
    (hleft : ∀ a ∈ L, ∀ b ∈ L, a * b * z = 0)
    (hright : ∀ a ∈ L, ∀ b ∈ L, z * a * b = 0)
    (hc : Commute (L.map (1 + ·)).prod z) :
    (L.map (fun a => a * z - z * a)).sum = 0 := by
  have he := hc.eq
  rw [prod_mul L z hleft, mul_prod L z hright] at he
  have hh := add_left_cancel he
  have hs : (L.map (fun a => a * z - z * a)).sum =
      (L.map (· * z)).sum - (L.map (z * ·)).sum := by
    clear hleft hright hc he hh
    induction L with
    | nil => simp
    | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; abel
  rw [hs, hh, sub_self]
end Theory.LinearAlgebra.ThreeBlockProduct
