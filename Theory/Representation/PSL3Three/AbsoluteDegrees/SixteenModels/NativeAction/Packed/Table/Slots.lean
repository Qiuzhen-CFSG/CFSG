module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowData

/-!
# Arithmetic of twelve-bit row-index slots

The native table stores sixteen row indices in one natural number. Mapping
these slots and bounding them can be checked as scalar natural-number facts.
The two induction lemmas recover each coordinate, avoiding repeated vector
construction in the kernel. These helpers are used by the actual certificate
assembly in `Table`; they make no assertion about packed field arithmetic.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

@[expose] def slot : ℕ → ℕ → ℕ
  | 0, r => r % 4096
  | j + 1, r => slot j (r / 4096)

@[expose] def mapSlots (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, r => f (r % 4096) % 4096 + 4096 * mapSlots f n (r / 4096)

@[expose] def boundedSlots : ℕ → ℕ → Bool
  | 0, _ => true
  | n + 1, r => decide (r % 4096 < 2808) && boundedSlots n (r / 4096)

theorem slot_eq (j r : ℕ) : slot j r = r / 4096 ^ j % 4096 := by
  induction j generalizing r with
  | zero => simp [slot]
  | succ j ih =>
    simp only [slot, ih, Nat.pow_succ', Nat.div_div_eq_div_mul]

theorem slot_mapSlots (f : ℕ → ℕ) (n j r : ℕ) (hj : j < n) :
    slot j (mapSlots f n r) = f (slot j r) % 4096 := by
  induction n generalizing j r with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => simp [slot, mapSlots, Nat.add_mod]
    | succ j =>
      simp only [slot, mapSlots, Nat.add_mul_div_left _ _ (by decide : 0 < 4096),
        Nat.div_eq_of_lt (Nat.mod_lt _ (by decide : 0 < 4096)), Nat.zero_add]
      exact ih j (r / 4096) (by omega)

theorem slot_lt_of_bounded (n j r : ℕ) (hj : j < n) (h : boundedSlots n r = true) :
    slot j r < 2808 := by
  induction n generalizing j r with
  | zero => omega
  | succ n ih =>
    have hh := Bool.and_eq_true_iff.mp h
    cases j with
    | zero => exact of_decide_eq_true hh.1
    | succ j => exact ih j (r / 4096) (by omega) hh.2


end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
