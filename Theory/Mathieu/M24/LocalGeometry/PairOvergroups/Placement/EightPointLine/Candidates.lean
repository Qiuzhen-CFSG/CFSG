module

public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.EightPointLine.Coordinates

/-!
# Candidate elementary nines and their diagonal lines

The two commuting generators of each candidate have nine distinct normal
forms. The generator relations prove that these are the entire generated
subgroup. The product of the generators has order three and generates its
diagonal line. These are intrinsic subgroup facts; exhaustive coverage and
invariance under a Sylow normalizer are separate obligations.

Source application: Aschbacher–Smith, proof of 1.3.4, printed p.511;
GLS3, Table 5.3e.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.EightPoint
open Subgroup

/-- The candidate Sylow three-subgroup specified by the two triples. -/
def nineGroup (i : Fin 280) : Subgroup Alt := closure (Set.range (nineGenerator i))

private def nineNext (j : Fin 9) (k : Fin 2) : Fin 9 :=
  ⟨if k = 0 then (j.val % 3 + 1) % 3 + 3 * (j.val / 3)
    else j.val % 3 + 3 * ((j.val / 3 + 1) % 3), by split_ifs <;> omega⟩

private theorem nineWord_step (i : Fin 280) (j : Fin 9) (k : Fin 2) :
    nineWord i j * nineGenerator i k = nineWord i (nineNext j k) := by
  have h0 : ∀ j : Fin 9,
      (nineNext j 0).val % 3 = (j.val % 3 + 1) % 3 ∧
      (nineNext j 0).val / 3 = j.val / 3 := by decide +kernel
  have h1 : ∀ j : Fin 9,
      (nineNext j 1).val % 3 = j.val % 3 ∧
      (nineNext j 1).val / 3 = (j.val / 3 + 1) % 3 := by decide +kernel
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · simp only [nineWord, (h0 j).1, (h0 j).2]
    rw [((nineGenerator_commute i).symm.pow_left (j.val / 3)).right_comm,
      ← pow_succ, pow_eq_pow_mod (j.val % 3 + 1) (nineGenerator_cube i 0)]
  · simp only [nineWord, (h1 j).1, (h1 j).2]
    rw [mul_assoc, ← pow_succ,
      pow_eq_pow_mod (j.val / 3 + 1) (nineGenerator_cube i 1)]

private theorem nineGenerator_inv (i : Fin 280) (k : Fin 2) :
    (nineGenerator i k)⁻¹ = nineGenerator i k * nineGenerator i k :=
  inv_eq_of_mul_eq_one_left (by simpa [pow_succ] using nineGenerator_cube i k)

theorem nineGenerator_mem (i : Fin 280) (k : Fin 2) :
    nineGenerator i k ∈ nineGroup i := subset_closure ⟨k, rfl⟩

theorem nineWord_mem (i : Fin 280) (j : Fin 9) : nineWord i j ∈ nineGroup i :=
  (nineGroup i).mul_mem ((nineGroup i).pow_mem (nineGenerator_mem i 0) _)
    ((nineGroup i).pow_mem (nineGenerator_mem i 1) _)

theorem mem_nineGroup (i : Fin 280) (g : Alt) :
    g ∈ nineGroup i ↔ ∃ j, nineWord i j = g := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction_right with
    | one => exact ⟨0, by simp [nineWord]⟩
    | mul_right x hx y hy ih =>
      obtain ⟨j, rfl⟩ := ih
      obtain ⟨k, rfl⟩ := hy
      exact ⟨nineNext j k, (nineWord_step i j k).symm⟩
    | mul_inv_cancel x hx y hy ih =>
      obtain ⟨j, rfl⟩ := ih
      obtain ⟨k, rfl⟩ := hy
      rw [nineGenerator_inv, ← mul_assoc, nineWord_step, nineWord_step]
      exact ⟨_, rfl⟩
  · rintro ⟨j, rfl⟩
    exact nineWord_mem i j

theorem card_nineGroup (i : Fin 280) : Nat.card (nineGroup i) = 9 := by
  have e : nineGroup i ≃ Set.range (nineWord i) :=
    Equiv.setCongr (by ext g; exact mem_nineGroup i g)
  rw [Nat.card_congr e,
    ← Nat.card_congr (Equiv.ofInjective (nineWord i) (nineWord_injective i))]
  simp

/-- The diagonal cyclic subgroup, a proposed invariant line. -/
def nineLine (i : Fin 280) : Subgroup Alt := zpowers (nineWord i 4)

theorem nineLine_le (i : Fin 280) : nineLine i ≤ nineGroup i :=
  zpowers_le.mpr (nineWord_mem i 4)

private theorem diagonal_order_data (i : Fin 280) :
    nineWord i 4 ^ 3 = 1 ∧ nineWord i 4 ≠ 1 := by
  constructor
  · change (nineGenerator i 0 * nineGenerator i 1) ^ 3 = 1
    rw [(nineGenerator_commute i).mul_pow, nineGenerator_cube, nineGenerator_cube, mul_one]
  · intro h
    have he : nineWord i 4 = nineWord i 0 := by simpa [nineWord] using h
    exact (by decide : (4 : Fin 9) ≠ 0) (nineWord_injective i he)

theorem card_nineLine (i : Fin 280) : Nat.card (nineLine i) = 3 := by
  rw [nineLine, Nat.card_zpowers]
  exact orderOf_eq_prime (diagonal_order_data i).1 (diagonal_order_data i).2

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.EightPoint
end
