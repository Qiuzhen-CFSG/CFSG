module

public import Theory.SpecificGroups.ReeTwo.Sylow

/-!
# Collected polynomial operations in the Ree two Sylow group

The polynomial root-one action is checked against the specified action on the
core. Iteration yields the cyclic-four action, and therefore the multiplication,
inversion, and powers of the existing Sylow model. These formulas allow finite
coordinate certificates to avoid repeatedly expanding root normal words.

Source: Shinoda (1975), (2.3), pp. 81–82, via `Core` and `RootAction`.
The action polynomial and its proof are adapted from the private implementation
in `TwistedParityPowerCounts` in this repository.
-/

namespace ReeTwo.SylowModel

@[expose] public def collectedActionStep (x : Core) : Core where
  b0 := x.b0
  b1 := x.b0 + x.b1
  b2 := x.b0 + x.b1 + x.b2
  b3 := x.b1 + x.b3
  b4 := x.b0 + x.b1 + x.b3 + x.b4
  b5 := x.b0 + x.b0 * x.b1 + x.b5
  b6 := x.b0 + x.b1 + x.b0 * x.b1 + x.b5 + x.b6
  b7 := x.b0 + x.b0 * x.b1 + x.b1 * x.b2 + x.b6 + x.b7
  b8 := x.b0 + x.b1 + x.b0 * x.b2 + x.b1 * x.b2 + x.b1 * x.b3 + x.b5 + x.b6 + x.b7 + x.b8
  b9 := x.b0 + x.b1 + x.b0 * x.b2 + x.b1 * x.b2 + x.b1 * x.b3 + x.b0 * x.b4 +
    x.b0 * x.b1 * x.b4 + x.b5 + x.b6 + x.b9

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
public theorem collectedActionStep_eq : ∀ x : Core, collectedActionStep x = Core.a x := by decide +kernel

@[expose] public def collectedAction (t : FiveFour.Cyclic 4) (x : Core) : Core :=
  (collectedActionStep^[t.toAdd.val]) x

public theorem collectedAction_eq (t : FiveFour.Cyclic 4) (x : Core) :
    collectedAction t x = Core.complementAction (SemidirectProduct.inr t) x := by
  change (collectedActionStep^[t.toAdd.val]) x = (Core.a ^ t.toAdd.val) x
  generalize t.toAdd.val = n
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, collectedActionStep_eq, pow_succ]
    rfl

@[expose] public def collectedMul (x y : SylowModel) : SylowModel :=
  ⟨x.left * collectedAction x.right y.left, x.right * y.right⟩

public theorem collectedMul_eq (x y : SylowModel) : collectedMul x y = x * y := by
  apply SemidirectProduct.ext
  · exact congrArg (x.left * ·) (collectedAction_eq x.right y.left)
  · rfl

@[expose] public def collectedPow (x : SylowModel) : ℕ → SylowModel
  | 0 => 1
  | n + 1 => collectedMul (collectedPow x n) x

public theorem collectedPow_eq (x : SylowModel) (n : ℕ) : collectedPow x n = x ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [collectedPow, collectedMul_eq, ih, pow_succ]

/-- Collected inversion, with the inverse cyclic action on the inverse core. -/
@[expose] public def collectedInv (x : SylowModel) : SylowModel :=
  ⟨collectedAction x.right⁻¹ x.left⁻¹, x.right⁻¹⟩

public theorem collectedInv_eq (x : SylowModel) : collectedInv x = x⁻¹ := by
  apply SemidirectProduct.ext
  · exact collectedAction_eq _ _
  · rfl

end ReeTwo.SylowModel
