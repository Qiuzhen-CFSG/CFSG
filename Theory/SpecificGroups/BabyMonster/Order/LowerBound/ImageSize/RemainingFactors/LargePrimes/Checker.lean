module

public import Theory.LinearAlgebra.PackedBinaryRows
public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.RemainingFactors.LargePrimes.Packed

/-!
# Checking saved Baby Monster vector actions in chunks

The packed action is assembled from independently checked row intervals.
`rowProduct_extend` consumes a previous prefix, the next interval and one
concrete XOR equality. Thus no certificate reduces a dense `Matrix.vecMul`,
or even the entire 4370-step packed action in one kernel reduction.
`action_eq_of_prefix` finishes the assembly, and `vecMul_eq_of_action` gives
the corresponding matrix action when needed.

The ATLAS row convention and source attribution are in `LowerBound/source/README.md`.
-/

@[expose] public section

namespace BabyMonster.OrderLowerBound.RemainingFactors.LargePrimes
open PackedBinaryRows

lemma rowProduct_add (x : ℕ) (r : ℕ → ℕ) (start n : ℕ) :
    rowProduct x r (start+n) = rowProduct x r start ^^^ rowRange x r start n := by
  induction n with
  | zero => simp [rowRange]
  | succ n ih =>
    change (rowProduct x r (start+n) ^^^ _) = rowProduct x r start ^^^ (rowRange x r start n ^^^ _)
    rw [ih, Nat.xor_assoc]
    rfl

lemma rowProduct_extend {x : ℕ} {r : ℕ → ℕ} {start n a b c : ℕ}
    (ha : rowProduct x r start = a) (hb : rowRange x r start n = b)
    (hc : a ^^^ b = c) : rowProduct x r (start+n) = c := by
  rw [rowProduct_add, ha, hb, hc]


/-- Finish a chain of interval evaluations covering all source rows. -/
theorem action_eq_of_prefix {b : Bool} {x y : Nat}
    (h : rowProduct x (rows b) 4370 = y) : action b x = y := h

/-- Transfer a checked packed action to the public matrix action. -/
theorem vecMul_eq_of_action {b : Bool} {x y : Nat} (h : action b x = y) :
    Matrix.vecMul (vector x) (if b then atlasB else atlasA) = vector y := by
  rw [← action_correct, h]

end BabyMonster.OrderLowerBound.RemainingFactors.LargePrimes
