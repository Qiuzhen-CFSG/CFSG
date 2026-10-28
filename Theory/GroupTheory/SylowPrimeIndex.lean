module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Index

/-!
# Overgroups of a Sylow subgroup of prime index

If a Sylow two-subgroup has prime index, every subgroup containing it is
either a two-group or the whole group. Relative indices multiply, so a
proper intermediate subgroup has the same index and equals the Sylow.
The concrete groups of orders ten and twenty have Sylow index five.

Source application: Aschbacher--Smith15.2.5, printed p.1107, the order-five
residual rows before the extra cubic Fitting factor.
-/
public section
open Subgroup
namespace Subgroup
variable {D : Type*} [Group D] [Finite D]

omit [Finite D] in
theorem eq_top_of_sylow_le_of_prime_index (P : Sylow 2 D) (A : Subgroup D)
    (hPA : (P : Subgroup D) ≤ A) (hA : ¬ IsPGroup 2 A)
    (hp : Nat.Prime (P : Subgroup D).index) : A = ⊤ := by
  rcases (Nat.dvd_prime hp).mp (index_dvd_of_le hPA) with h1 | he
  · exact index_eq_one.mp h1
  · have hrel : (P : Subgroup D).relIndex A = 1 := by
      have hh := relIndex_mul_index hPA
      rw [he] at hh
      exact Nat.eq_of_mul_eq_mul_right hp.pos (by simpa using hh)
    have heq : (P : Subgroup D) = A := le_antisymm hPA (relIndex_eq_one.mp hrel)
    exact (hA (heq ▸ P.isPGroup')).elim

theorem sylow_index_five_of_card_ten_or_twenty (P : Sylow 2 D)
    (hc : Nat.card D = 10 ∨ Nat.card D = 20) : (P : Subgroup D).index = 5 := by
  have hm := (P : Subgroup D).index_mul_card
  rcases hc with hc | hc
  · have hP : Nat.card P = 2 := by
      rw [P.card_eq_multiplicity, hc]
      decide +kernel
    rw [hc,hP] at hm
    omega
  · have hP : Nat.card P = 4 := by
      rw [P.card_eq_multiplicity, hc]
      decide +kernel
    rw [hc,hP] at hm
    omega
end Subgroup
