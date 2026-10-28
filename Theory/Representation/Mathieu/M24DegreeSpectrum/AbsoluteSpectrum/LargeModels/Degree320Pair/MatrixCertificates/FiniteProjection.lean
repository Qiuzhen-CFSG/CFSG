module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Recovering a projection from an invertible complementary sum

Let `T` belong to a subalgebra of a finite ring and let `E` be idempotent,
with `T E = E T = 0`. If `T + E` is a unit, some positive power equals one.
Expanding that power gives `T^k + E = 1`, so `E` belongs to the subalgebra.
This elementary argument avoids computing a characteristic polynomial.

The concrete ATLAS degree-320 application is in `ProjectionApplication.lean`;
its numerical source is attributed in `../source/README.md`.
-/

public section
namespace Subalgebra
variable {F R : Type*} [CommRing F] [Ring R] [Algebra F R] [Finite R]

theorem mem_of_idempotent_complement (S : Subalgebra F R) (T E : R)
    (hT : T ∈ S) (hTE : T * E = 0) (hET : E * T = 0)
    (hEE : E * E = E) (hu : IsUnit (T + E)) : E ∈ S := by
  let : Finite Rˣ := Finite.of_injective (fun u : Rˣ => (u : R)) Units.val_injective
  obtain ⟨n, hn, hp⟩ := hu.isOfFinOrder.exists_pow_eq_one
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have he (k : Nat) : (T + E) ^ (k + 1) = T ^ (k + 1) + E := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, add_mul, mul_add, mul_add, hET, hEE, zero_add]
      have hz : T ^ (k + 1) * E = 0 := by
        rw [pow_succ, mul_assoc, hTE, mul_zero]
      rw [hz, add_zero, ← pow_succ]
  rw [he] at hp
  have hE : E = 1 - T ^ (m + 1) := by rw [← hp]; simp
  rw [hE]
  exact S.sub_mem S.one_mem (S.pow_mem hT _)
end Subalgebra
