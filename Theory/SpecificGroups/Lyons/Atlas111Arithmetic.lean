module

public import Theory.SpecificGroups.Lyons.Atlas111Data
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Verified arithmetic for the Lyons matrix certificates

A dot product of two base-five packed vectors is computed over the natural
numbers and then reduced modulo five. `packedDot_eq` identifies it with the
usual dot product in `ZMod 5`. `allBelow_sound` and `row_sound` turn Boolean
row checks into matrix-entry equations. These are ordinary inductive proofs;
only the subsequent closed numerical certificates use kernel reduction.

The data format is documented in `Atlas111Source/README.md`.
-/

namespace Lyons.Atlas111Certificate

@[expose] public def packedDot : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, a, b => packedDot n a b + (a / 5 ^ n % 5) * (b / 5 ^ n % 5)

public theorem packedDot_eq (n a b : ℕ) :
    (packedDot n a b : ZMod 5) =
      ∑ j : Fin n, ((a / 5 ^ j.val : ℕ) : ZMod 5) * ((b / 5 ^ j.val : ℕ) : ZMod 5) := by
  induction n with
  | zero => simp [packedDot]
  | succ n ih =>
    simp only [packedDot, Nat.cast_add, Nat.cast_mul, ZMod.natCast_mod, ih,
      Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

@[expose] public def allBelow : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n + 1, p => allBelow n p && p n

public theorem allBelow_sound {n : ℕ} {p : ℕ → Bool} (h : allBelow n p = true) :
    ∀ i < n, p i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    simp only [allBelow, Bool.and_eq_true] at h
    intro i hi
    by_cases hin : i < n
    · exact ih h.1 i hin
    · have : i = n := by omega
      simpa [this] using h.2

@[expose] public def checkRow (rows columns : Fin 111 → ℕ) (i : Fin 111) : Bool :=
  allBelow 111 fun j => packedDot 111 (rows i) (columns (Fin.ofNat 111 j)) % 5 ==
    if j = i.val then 1 else 0

public theorem row_sound (rows columns : Fin 111 → ℕ) (i : Fin 111)
    (h : checkRow rows columns i = true) (j : Fin 111) :
    (packedDot 111 (rows i) (columns j) : ZMod 5) =
      (1 : Matrix (Fin 111) (Fin 111) (ZMod 5)) i j := by
  have h' := allBelow_sound h j.val j.isLt
  have hj : Fin.ofNat 111 j.val = j := by ext; exact Nat.mod_eq_of_lt j.isLt
  simp only [hj, beq_iff_eq] at h'
  rw [← ZMod.natCast_mod, h']
  by_cases hij : i = j
  · subst j; simp
  · have hne : j.val ≠ i.val := fun hval => hij (Fin.ext hval.symm)
    simp [hne, hij]

end Lyons.Atlas111Certificate
