module

public import GorensteinWalter.ASevenStructureFacts
import Mathlib.Tactic

/-!
# Odd-subgroup closure tests in the concrete alternating group on seven letters

The actor list enumerates the existing dihedral Sylow subgroup `a7S`.
The depth-zero test asks for odd cycle lengths. Each further test also checks
products with Sylow conjugates of an element and its inverse. An odd-order
subgroup normalized by `a7S` satisfies every depth of the test, by closure
and the divisibility of element orders and cycle lengths into subgroup order.

The explicit list records 71 proposed first-round candidates. This module
makes no completeness assertion about that list. The separate elimination
module supplies a checked obstruction for each listed element outside `a7U`.
These are concrete prerequisites for ABG, II.5 Lemma9(i), article p49
(PDF page50); the subgroup-family notation is on article p7.
The list was proposed by finite permutation enumeration; subsequent theorems,
not the generating program, establish the properties used in proofs.
-/

namespace GorensteinWalter

@[expose] public def a7OddClosureCandidates : List A7 := [
  ⟨1, by simp⟩,
  ⟨Equiv.swap (4 : Fin 7) 6 * Equiv.swap (4 : Fin 7) 5, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (4 : Fin 7) 5 * Equiv.swap (4 : Fin 7) 6, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (2 : Fin 7) 6 * Equiv.swap (2 : Fin 7) 3, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (2 : Fin 7) 3 * Equiv.swap (2 : Fin 7) 6, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (1 : Fin 7) 3 * Equiv.swap (1 : Fin 7) 5 * Equiv.swap (1 : Fin 7) 4 * Equiv.swap (1 : Fin 7) 2, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (1 : Fin 7) 4 * Equiv.swap (1 : Fin 7) 2, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (1 : Fin 7) 3 * Equiv.swap (1 : Fin 7) 4 * Equiv.swap (1 : Fin 7) 5 * Equiv.swap (1 : Fin 7) 2, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (1 : Fin 7) 5 * Equiv.swap (1 : Fin 7) 2, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (1 : Fin 7) 2 * Equiv.swap (1 : Fin 7) 5 * Equiv.swap (1 : Fin 7) 4 * Equiv.swap (1 : Fin 7) 3, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (1 : Fin 7) 2 * Equiv.swap (1 : Fin 7) 4 * Equiv.swap (1 : Fin 7) 5 * Equiv.swap (1 : Fin 7) 3, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (1 : Fin 7) 4 * Equiv.swap (1 : Fin 7) 3, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (1 : Fin 7) 5 * Equiv.swap (1 : Fin 7) 3, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (1 : Fin 7) 2 * Equiv.swap (1 : Fin 7) 4, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (1 : Fin 7) 3 * Equiv.swap (1 : Fin 7) 4, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (1 : Fin 7) 2 * Equiv.swap (1 : Fin 7) 5, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (1 : Fin 7) 3 * Equiv.swap (1 : Fin 7) 5, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 2 * Equiv.swap (0 : Fin 7) 1 * Equiv.swap (3 : Fin 7) 5 * Equiv.swap (3 : Fin 7) 4, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 2 * Equiv.swap (0 : Fin 7) 1 * Equiv.swap (3 : Fin 7) 4 * Equiv.swap (3 : Fin 7) 5, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 4 * Equiv.swap (0 : Fin 7) 3 * Equiv.swap (0 : Fin 7) 2 * Equiv.swap (0 : Fin 7) 1, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 5 * Equiv.swap (0 : Fin 7) 3 * Equiv.swap (0 : Fin 7) 2 * Equiv.swap (0 : Fin 7) 1, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 3 * Equiv.swap (0 : Fin 7) 1 * Equiv.swap (2 : Fin 7) 5 * Equiv.swap (2 : Fin 7) 4, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 4 * Equiv.swap (0 : Fin 7) 2 * Equiv.swap (0 : Fin 7) 3 * Equiv.swap (0 : Fin 7) 1, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 3 * Equiv.swap (0 : Fin 7) 1 * Equiv.swap (2 : Fin 7) 4 * Equiv.swap (2 : Fin 7) 5, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 5 * Equiv.swap (0 : Fin 7) 2 * Equiv.swap (0 : Fin 7) 3 * Equiv.swap (0 : Fin 7) 1, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 2 * Equiv.swap (0 : Fin 7) 3 * Equiv.swap (0 : Fin 7) 4 * Equiv.swap (0 : Fin 7) 1, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 3 * Equiv.swap (0 : Fin 7) 2 * Equiv.swap (0 : Fin 7) 4 * Equiv.swap (0 : Fin 7) 1, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 2 * Equiv.swap (0 : Fin 7) 3 * Equiv.swap (0 : Fin 7) 5 * Equiv.swap (0 : Fin 7) 1, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 3 * Equiv.swap (0 : Fin 7) 2 * Equiv.swap (0 : Fin 7) 5 * Equiv.swap (0 : Fin 7) 1, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 6 * Equiv.swap (0 : Fin 7) 1, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 1 * Equiv.swap (0 : Fin 7) 2 * Equiv.swap (3 : Fin 7) 5 * Equiv.swap (3 : Fin 7) 4, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 1 * Equiv.swap (0 : Fin 7) 2 * Equiv.swap (3 : Fin 7) 4 * Equiv.swap (3 : Fin 7) 5, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 1 * Equiv.swap (0 : Fin 7) 4 * Equiv.swap (0 : Fin 7) 3 * Equiv.swap (0 : Fin 7) 2, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 1 * Equiv.swap (0 : Fin 7) 5 * Equiv.swap (0 : Fin 7) 3 * Equiv.swap (0 : Fin 7) 2, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 3 * Equiv.swap (0 : Fin 7) 5 * Equiv.swap (0 : Fin 7) 4 * Equiv.swap (0 : Fin 7) 2, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 4 * Equiv.swap (0 : Fin 7) 2, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 3 * Equiv.swap (0 : Fin 7) 4 * Equiv.swap (0 : Fin 7) 5 * Equiv.swap (0 : Fin 7) 2, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 5 * Equiv.swap (0 : Fin 7) 2, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 5 * Equiv.swap (0 : Fin 7) 4 * Equiv.swap (0 : Fin 7) 1 * Equiv.swap (0 : Fin 7) 2, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 3 * Equiv.swap (0 : Fin 7) 2 * Equiv.swap (1 : Fin 7) 5 * Equiv.swap (1 : Fin 7) 4, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 4 * Equiv.swap (0 : Fin 7) 5 * Equiv.swap (0 : Fin 7) 1 * Equiv.swap (0 : Fin 7) 2, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 3 * Equiv.swap (0 : Fin 7) 2 * Equiv.swap (1 : Fin 7) 4 * Equiv.swap (1 : Fin 7) 5, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 1 * Equiv.swap (0 : Fin 7) 3 * Equiv.swap (2 : Fin 7) 5 * Equiv.swap (2 : Fin 7) 4, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 1 * Equiv.swap (0 : Fin 7) 4 * Equiv.swap (0 : Fin 7) 2 * Equiv.swap (0 : Fin 7) 3, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 1 * Equiv.swap (0 : Fin 7) 3 * Equiv.swap (2 : Fin 7) 4 * Equiv.swap (2 : Fin 7) 5, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 1 * Equiv.swap (0 : Fin 7) 5 * Equiv.swap (0 : Fin 7) 2 * Equiv.swap (0 : Fin 7) 3, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 2 * Equiv.swap (0 : Fin 7) 5 * Equiv.swap (0 : Fin 7) 4 * Equiv.swap (0 : Fin 7) 3, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 2 * Equiv.swap (0 : Fin 7) 4 * Equiv.swap (0 : Fin 7) 5 * Equiv.swap (0 : Fin 7) 3, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 4 * Equiv.swap (0 : Fin 7) 3, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 5 * Equiv.swap (0 : Fin 7) 3, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 2 * Equiv.swap (0 : Fin 7) 3 * Equiv.swap (1 : Fin 7) 5 * Equiv.swap (1 : Fin 7) 4, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 5 * Equiv.swap (0 : Fin 7) 4 * Equiv.swap (0 : Fin 7) 1 * Equiv.swap (0 : Fin 7) 3, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 2 * Equiv.swap (0 : Fin 7) 3 * Equiv.swap (1 : Fin 7) 4 * Equiv.swap (1 : Fin 7) 5, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 4 * Equiv.swap (0 : Fin 7) 5 * Equiv.swap (0 : Fin 7) 1 * Equiv.swap (0 : Fin 7) 3, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 1 * Equiv.swap (0 : Fin 7) 2 * Equiv.swap (0 : Fin 7) 3 * Equiv.swap (0 : Fin 7) 4, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 1 * Equiv.swap (0 : Fin 7) 3 * Equiv.swap (0 : Fin 7) 2 * Equiv.swap (0 : Fin 7) 4, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 2 * Equiv.swap (0 : Fin 7) 4, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 3 * Equiv.swap (0 : Fin 7) 4, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 2 * Equiv.swap (0 : Fin 7) 1 * Equiv.swap (0 : Fin 7) 5 * Equiv.swap (0 : Fin 7) 4, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 5 * Equiv.swap (0 : Fin 7) 4 * Equiv.swap (1 : Fin 7) 3 * Equiv.swap (1 : Fin 7) 2, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 5 * Equiv.swap (0 : Fin 7) 4 * Equiv.swap (1 : Fin 7) 2 * Equiv.swap (1 : Fin 7) 3, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 3 * Equiv.swap (0 : Fin 7) 1 * Equiv.swap (0 : Fin 7) 5 * Equiv.swap (0 : Fin 7) 4, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 1 * Equiv.swap (0 : Fin 7) 2 * Equiv.swap (0 : Fin 7) 3 * Equiv.swap (0 : Fin 7) 5, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 1 * Equiv.swap (0 : Fin 7) 3 * Equiv.swap (0 : Fin 7) 2 * Equiv.swap (0 : Fin 7) 5, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 2 * Equiv.swap (0 : Fin 7) 5, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 3 * Equiv.swap (0 : Fin 7) 5, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 2 * Equiv.swap (0 : Fin 7) 1 * Equiv.swap (0 : Fin 7) 4 * Equiv.swap (0 : Fin 7) 5, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 4 * Equiv.swap (0 : Fin 7) 5 * Equiv.swap (1 : Fin 7) 3 * Equiv.swap (1 : Fin 7) 2, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 4 * Equiv.swap (0 : Fin 7) 5 * Equiv.swap (1 : Fin 7) 2 * Equiv.swap (1 : Fin 7) 3, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 3 * Equiv.swap (0 : Fin 7) 1 * Equiv.swap (0 : Fin 7) 4 * Equiv.swap (0 : Fin 7) 5, by simp [Equiv.Perm.sign_mul]⟩,
  ⟨Equiv.swap (0 : Fin 7) 1 * Equiv.swap (0 : Fin 7) 6, by simp [Equiv.Perm.sign_mul]⟩]

@[expose] public def a7OddClosureActors : Fin 8 → A7 :=
  ![1, a7v, a7v ^ 2, a7v ^ 3, a7s, a7s * a7v, a7s * a7v ^ 2,
    a7s * a7v ^ 3]

@[expose] public def a7OddClosureTest : ℕ → A7 → Prop
  | 0, x => ∀ length ∈ (x : Equiv.Perm (Fin 7)).cycleType, Odd length
  | depth + 1, x => a7OddClosureTest depth x ∧ ∀ index : Fin 8,
      a7OddClosureTest depth (x * (a7OddClosureActors index * x * (a7OddClosureActors index)⁻¹)) ∧
      a7OddClosureTest depth (x * (a7OddClosureActors index * x⁻¹ * (a7OddClosureActors index)⁻¹))

public instance (depth : ℕ) (x : A7) : Decidable (a7OddClosureTest depth x) := by
  induction depth generalizing x with
  | zero => unfold a7OddClosureTest; infer_instance
  | succ depth ih => unfold a7OddClosureTest; infer_instance

private theorem a7OddClosureActors_mem (index : Fin 8) :
    a7OddClosureActors index ∈ a7S := by
  fin_cases index <;>
    change _ = 1 ∨ _ = a7v ∨ _ = a7v ^ 2 ∨ _ = a7v ^ 3 ∨
      _ = a7s ∨ _ = a7s * a7v ∨ _ = a7s * a7v ^ 2 ∨ _ = a7s * a7v ^ 3
  all_goals decide

public theorem a7_oddClosureTest_of_mem (K : Subgroup A7) (hodd : Odd (Nat.card K))
    (hnorm : a7S ≤ Subgroup.normalizer (K : Set A7))
    (depth : ℕ) (x : A7) (hx : x ∈ K) : a7OddClosureTest depth x := by
  induction depth generalizing x with
  | zero =>
    intro length hlength
    have hxo : Odd (orderOf x) :=
      Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard K hx)
    have hxperm : Odd (orderOf (x : Equiv.Perm (Fin 7))) := by
      simpa only [Subgroup.orderOf_coe] using hxo
    exact Odd.of_dvd_nat hxperm (Equiv.Perm.dvd_of_mem_cycleType hlength)
  | succ depth ih =>
    refine ⟨ih x hx, fun index => ⟨?_, ?_⟩⟩
    · apply ih
      exact K.mul_mem hx ((Subgroup.mem_normalizer_iff.mp
        (hnorm (a7OddClosureActors_mem index)) x).mp hx)
    · apply ih
      exact K.mul_mem hx ((Subgroup.mem_normalizer_iff.mp
        (hnorm (a7OddClosureActors_mem index)) x⁻¹).mp (K.inv_mem hx))

end GorensteinWalter
