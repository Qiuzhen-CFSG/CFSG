module
public import Mathlib.GroupTheory.Index

/-!
# Prime-to-p index from an action with prime-to-p kernel

For a normal subgroup N, the index of N factors through N ker(f).
Its first factor divides the order of ker(f), and its second factor
divides the index of f(N). Thus prime-to-p bounds for the full kernel
and image index give the original index bound without discarding a kernel.

This elementary index calculation is used for the original point-centralizer
HS action in Aschbacher--Smith 12.6.12, printed pp.825--826.
-/

public section

namespace Subgroup
/-- A prime-to-p image index and full kernel order imply prime-to-p index upstairs. -/
theorem index_coprime_of_map_index_and_kernel
    {A B : Type*} [Group A] [Group B] [Finite A]
    (p : ℕ) (f : A →* B) (N : Subgroup A) [N.Normal]
    (hk : Nat.Coprime p (Nat.card f.ker))
    (hi : Nat.Coprime p (N.map f).index) : Nat.Coprime p N.index := by
  have hsup : Nat.Coprime p (N ⊔ f.ker).index :=
    hi.of_dvd_right ⟨f.range.index,N.index_map f⟩
  rw [←relIndex_mul_index (show N ≤ N ⊔ f.ker from le_sup_left)]
  apply Nat.Coprime.mul_right _ hsup
  rw [relIndex_sup_left]
  exact hk.of_dvd_right (relIndex_dvd_card _ _)
end Subgroup
