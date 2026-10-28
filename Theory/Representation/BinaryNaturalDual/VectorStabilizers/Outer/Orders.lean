module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Outer.Witness
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Orders of the nonsingular full stabilizers

The actual inner subgroup has index two; restriction to the covector kernel
identifies it with GL in one lower dimension. Counting ordered bases therefore
gives 336 in dimension four and 40320 in dimension five. These are consequences
of the proved subgroup maps, independent of the automorphism-group recognition.

Source: Aschbacher–Smith, H.9.1(4), printed p.390.
-/

public section
namespace BinaryNaturalDual.VectorStabilizers
open BinaryLinear.OuterCyclic

/-- The order of the full stabilizer is twice that of the kernel linear group. -/
theorem fullStabilizer_card {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    Nat.card (fullStabilizer d (x,f)) = 2 * Nat.card (LinearGroup (n - 1)) := by
  have hc := (innerInFull d (x,f)).index_mul_card
  rw [innerInFull_index hn d h,
    Nat.card_congr ((innerInFullEquiv d (x,f)).trans
      (innerStabilizerEquivLinear d h)).toEquiv] at hc
  exact hc.symm

/-- The degree-four nonsingular stabilizer has order 336. -/
theorem fullStabilizer_card_four (d : CoordinateAction 4)
    {x : BinaryLinear.OuterCyclic.Space 4}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space 4)} (h : f x = 1) :
    Nat.card (fullStabilizer d (x,f)) = 336 := by
  rw [fullStabilizer_card (Or.inl rfl) d h,
    ← Nat.card_congr (matrixEquivLinear (4 - 1)).toEquiv, Matrix.card_GL_field]
  decide

/-- The degree-five nonsingular stabilizer has order 40320. -/
theorem fullStabilizer_card_five (d : CoordinateAction 5)
    {x : BinaryLinear.OuterCyclic.Space 5}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space 5)} (h : f x = 1) :
    Nat.card (fullStabilizer d (x,f)) = 40320 := by
  rw [fullStabilizer_card (Or.inr rfl) d h,
    ← Nat.card_congr (matrixEquivLinear (5 - 1)).toEquiv, Matrix.card_GL_field]
  decide

end BinaryNaturalDual.VectorStabilizers
