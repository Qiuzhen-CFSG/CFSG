module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.Perm.List
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases

namespace Sporadic.Mathieu

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- The first ATLAS standard generator for the degree-11 representation:
`(2,10)(4,11)(5,7)(8,9)`. -/
@[expose]
public def m11GeneratorA : Equiv.Perm (Fin 11) :=
  Equiv.swap (2 : Fin 11) 10 * Equiv.swap (4 : Fin 11) 11 *
    Equiv.swap (5 : Fin 11) 7 * Equiv.swap (8 : Fin 11) 9

/-- The second ATLAS standard generator for the degree-11 representation:
`(1,4,3,8)(2,5,6,9)`. -/
@[expose]
public def m11GeneratorB : Equiv.Perm (Fin 11) :=
  List.formPerm [1, 4, 3, 8] * List.formPerm [2, 5, 6, 9]

private def m11A₁ : Equiv.Perm (Fin 11) := Equiv.swap (2 : Fin 11) 10
private def m11A₂ : Equiv.Perm (Fin 11) := Equiv.swap (4 : Fin 11) 11
private def m11A₃ : Equiv.Perm (Fin 11) := Equiv.swap (5 : Fin 11) 7
private def m11A₄ : Equiv.Perm (Fin 11) := Equiv.swap (8 : Fin 11) 9

private theorem m11A₁_disjoint_A₂ : Equiv.Perm.Disjoint m11A₁ m11A₂ := by
  change Equiv.Perm.Disjoint (Equiv.swap (2 : Fin 11) 10) (Equiv.swap (4 : Fin 11) 11)
  exact Equiv.Perm.disjoint_swap_swap (by simp)
private theorem m11A₁_disjoint_A₃ : Equiv.Perm.Disjoint m11A₁ m11A₃ := by
  change Equiv.Perm.Disjoint (Equiv.swap (2 : Fin 11) 10) (Equiv.swap (5 : Fin 11) 7)
  exact Equiv.Perm.disjoint_swap_swap (by simp)
private theorem m11A₁_disjoint_A₄ : Equiv.Perm.Disjoint m11A₁ m11A₄ := by
  change Equiv.Perm.Disjoint (Equiv.swap (2 : Fin 11) 10) (Equiv.swap (8 : Fin 11) 9)
  exact Equiv.Perm.disjoint_swap_swap (by simp)
private theorem m11A₂_disjoint_A₃ : Equiv.Perm.Disjoint m11A₂ m11A₃ := by
  change Equiv.Perm.Disjoint (Equiv.swap (4 : Fin 11) 11) (Equiv.swap (5 : Fin 11) 7)
  exact Equiv.Perm.disjoint_swap_swap (by simp)
private theorem m11A₂_disjoint_A₄ : Equiv.Perm.Disjoint m11A₂ m11A₄ := by
  change Equiv.Perm.Disjoint (Equiv.swap (4 : Fin 11) 11) (Equiv.swap (8 : Fin 11) 9)
  exact Equiv.Perm.disjoint_swap_swap (by simp)
private theorem m11A₃_disjoint_A₄ : Equiv.Perm.Disjoint m11A₃ m11A₄ := by
  change Equiv.Perm.Disjoint (Equiv.swap (5 : Fin 11) 7) (Equiv.swap (8 : Fin 11) 9)
  exact Equiv.Perm.disjoint_swap_swap (by simp)

private theorem m11A12_disjoint_A34 :
    Equiv.Perm.Disjoint (m11A₁ * m11A₂) (m11A₃ * m11A₄) := by
  exact m11A₁_disjoint_A₃.mul_right m11A₁_disjoint_A₄ |>.mul_left
    (m11A₂_disjoint_A₃.mul_right m11A₂_disjoint_A₄)

private theorem m11_swap_sq (x y : Fin 11) : (Equiv.swap x y) ^ 2 = 1 := by
  apply Equiv.ext
  intro z
  change Equiv.swap x y (Equiv.swap x y z) = z
  exact Equiv.swap_apply_self x y z

private theorem m11GeneratorA_sq : m11GeneratorA ^ 2 = 1 := by
  have hA₁ : m11A₁ ^ 2 = 1 := by
    simpa [m11A₁] using m11_swap_sq (2 : Fin 11) 10
  have hA₂ : m11A₂ ^ 2 = 1 := by
    simpa [m11A₂] using m11_swap_sq (4 : Fin 11) 11
  have hA₃ : m11A₃ ^ 2 = 1 := by
    simpa [m11A₃] using m11_swap_sq (5 : Fin 11) 7
  have hA₄ : m11A₄ ^ 2 = 1 := by
    simpa [m11A₄] using m11_swap_sq (8 : Fin 11) 9
  have h12 : (m11A₁ * m11A₂) ^ 2 = 1 := by
    rw [m11A₁_disjoint_A₂.commute.mul_pow, hA₁, hA₂]
    simp
  have h34 : (m11A₃ * m11A₄) ^ 2 = 1 := by
    rw [m11A₃_disjoint_A₄.commute.mul_pow, hA₃, hA₄]
    simp
  rw [show m11GeneratorA = (m11A₁ * m11A₂) * (m11A₃ * m11A₄) by
    simp [m11GeneratorA, m11A₁, m11A₂, m11A₃, m11A₄, mul_assoc],
    m11A12_disjoint_A34.commute.mul_pow, h12, h34]
  simp

/-- The first ATLAS standard generator has order two. -/
public theorem m11GeneratorA_order : orderOf m11GeneratorA = 2 := by
  apply orderOf_eq_prime
  · exact m11GeneratorA_sq
  · intro h
    have hx := DFunLike.congr_fun h (2 : Fin 11)
    simp [m11GeneratorA, Equiv.swap_apply_def] at hx

private def m11B₁ : Equiv.Perm (Fin 11) := List.formPerm [1, 4, 3, 8]
private def m11B₂ : Equiv.Perm (Fin 11) := List.formPerm [2, 5, 6, 9]
private theorem m11B₁_nodup : ([1, 4, 3, 8] : List (Fin 11)).Nodup := by simp
private theorem m11B₂_nodup : ([2, 5, 6, 9] : List (Fin 11)).Nodup := by simp
private theorem m11B₁_pow : m11B₁ ^ 4 = 1 := by
  exact List.formPerm_pow_length_eq_one_of_nodup ([1, 4, 3, 8] : List (Fin 11)) m11B₁_nodup
private theorem m11B₂_pow : m11B₂ ^ 4 = 1 := by
  exact List.formPerm_pow_length_eq_one_of_nodup ([2, 5, 6, 9] : List (Fin 11)) m11B₂_nodup
private theorem m11B₁_disjoint_B₂ : Equiv.Perm.Disjoint m11B₁ m11B₂ := by
  apply (List.formPerm_disjoint_iff m11B₁_nodup m11B₂_nodup (by simp) (by simp)).mpr
  simp

/-- The second ATLAS standard generator has order four. -/
public theorem m11GeneratorB_order : orderOf m11GeneratorB = 4 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide +kernel : 0 < 4)
  · change (m11B₁ * m11B₂) ^ 4 = 1
    rw [m11B₁_disjoint_B₂.commute.mul_pow, m11B₁_pow, m11B₂_pow]
    simp
  · intro p hp hp4
    have hpPow : p ∣ 2 ^ 2 := by simpa using hp4
    have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow hpPow
    have hpEq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
    subst p
    intro h
    have hx := DFunLike.congr_fun h (1 : Fin 11)
    have h₁ : m11B₂ (1 : Fin 11) = 1 := by simp [m11B₂, Equiv.swap_apply_def]
    have h₂ : m11B₁ (1 : Fin 11) = 4 := by simp [m11B₁, Equiv.swap_apply_def]
    have h₃ : m11B₂ (4 : Fin 11) = 4 := by simp [m11B₂, Equiv.swap_apply_def]
    have h₄ : m11B₁ (4 : Fin 11) = 3 := by simp [m11B₁, Equiv.swap_apply_def]
    change (m11B₁ * m11B₂) ((m11B₁ * m11B₂) 1) = 1 at hx
    rw [show (m11B₁ * m11B₂) 1 = 4 by simp [Equiv.Perm.mul_apply, h₁, h₂],
      show (m11B₁ * m11B₂) 4 = 3 by simp [Equiv.Perm.mul_apply, h₃, h₄]] at hx
    cases hx

private def m11ABCycle : Equiv.Perm (Fin 11) :=
  List.formPerm [0, 4, 3, 9, 10, 2, 7, 5, 6, 8, 1]
private theorem m11GeneratorAB_eq_cycle :
    m11GeneratorA * m11GeneratorB = m11ABCycle := by
  ext x
  fin_cases x <;> rfl

/-- The product of the two ATLAS standard generators has order eleven. -/
public theorem m11GeneratorAB_order : orderOf (m11GeneratorA * m11GeneratorB) = 11 := by
  let : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
  apply orderOf_eq_prime
  · rw [m11GeneratorAB_eq_cycle]
    exact List.formPerm_pow_length_eq_one_of_nodup
      ([0, 4, 3, 9, 10, 2, 7, 5, 6, 8, 1] : List (Fin 11)) (by simp)
  · intro h
    have hx := DFunLike.congr_fun h (0 : Fin 11)
    have hmove : m11ABCycle 0 = 4 := by simp [m11ABCycle, Equiv.swap_apply_def]
    rw [m11GeneratorAB_eq_cycle, hmove] at hx
    cases hx

end Sporadic.Mathieu
