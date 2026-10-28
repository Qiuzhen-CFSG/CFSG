module
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.IntervalCases

/-!
# Odd squares in five-point groups with two-group kernel

An odd divisor of the order of a two-kernel cover of S₅ divides the image
order, hence 120. Its square must then divide the squarefree odd part 15.
Thus no nontrivial odd square divides the cover's order. This is the
order form of the cyclic odd Sylow obstruction in Aschbacher--Smith
13.6.14, printed pp.929--930.
-/

public section
open Subgroup
namespace SymmetricFive
variable {G : Type*} [Group G] [Finite G]

theorem odd_square_not_dvd_card_of_two_kernel
    (f : G →* Equiv.Perm (Fin 5)) (hf : IsPGroup 2 f.ker)
    {m : ℕ} (ho : Odd m) (hm : m ≠ 1) : ¬ m ^ 2 ∣ Nat.card G := by
  intro hd
  obtain ⟨n, hn⟩ := hf.exists_card_eq
  have hc : Nat.Coprime (m ^ 2) (2 ^ n) := ho.coprime_two_right.pow_left 2 |>.pow_right n
  have he := f.ker.card_mul_index
  rw [index_ker, hn] at he
  have hdim : m ^ 2 ∣ Nat.card f.range := hc.dvd_of_dvd_mul_left (he.symm ▸ hd)
  have h120 : m ^ 2 ∣ 120 := by
    have hS : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    exact hS ▸ hdim.trans f.range.card_subgroup_dvd_card
  have hc8 : Nat.Coprime (m ^ 2) (2 ^ 3) := ho.coprime_two_right.pow_left 2 |>.pow_right 3
  have h15 : m ^ 2 ∣ 15 := hc8.dvd_of_dvd_mul_left (by norm_num; exact h120)
  have hbound : m ≤ 3 := by
    have hh := Nat.le_of_dvd (by decide : 0 < 15) h15
    nlinarith
  interval_cases m <;> norm_num at *

end SymmetricFive
