module

public import Theory.AtlasPort.OtherSporadic.Fischer.ParkerLoopIdentities
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Logic.Equiv.Prod

/-!
# Inversion and translations in the concrete Parker loop

The inverse of a signed Golay word is obtained by adding its quarter-weight
parity to its sign. Alternation of the associator gives the inverse-property
identities, hence left and right translations are genuine permutations.
The adjoined zero is `none`, distinct from every loop element, including its
multiplicative identity `(0, 0)`. No associative group instance is imposed on
the Parker loop.

Source: Aschbacher, *Sporadic Groups*, Sections 12–14, especially the
permutations on p. 58. The Golay factor set and identities are the attributed
ATLAS ports imported above.
-/

@[expose] public section

noncomputable section

open Atlas.Fischer Atlas.Codes

namespace Sporadic.Monster.Construction.TrialitySpin

def loopOne : ParkerLoop := (0, 0)
def loopPi : ParkerLoop := (0, 1)
def loopInverse (x : ParkerLoop) : ParkerLoop := parkerSign (golayQuarterWeight x.1) x

private theorem bit_add_self (x : ParkerBit) : x + x = 0 := by
  have h : ∀ t : ParkerBit, t + t = 0 := by decide
  exact h x

@[simp] theorem loopInverse_one : loopInverse loopOne = loopOne := by
  simp [loopInverse, loopOne]

@[simp] theorem loopInverse_pi : loopInverse loopPi = loopPi := by
  simp [loopInverse, loopPi]

@[simp] theorem loopInverse_inverse (x : ParkerLoop) :
    loopInverse (loopInverse x) = x := by
  change parkerSign (golayQuarterWeight x.1)
    (parkerSign (golayQuarterWeight x.1) x) = x
  rw [parkerSign_add, bit_add_self, parkerSign_zero]

@[simp] theorem loopInverse_mul (x : ParkerLoop) :
    parkerLoopMultiply (loopInverse x) x = loopOne := by
  rw [loopInverse, parkerLoopMultiply_sign_left, parkerLoopMultiply_square]
  apply Prod.ext
  · rfl
  · exact bit_add_self _

@[simp] theorem mul_loopInverse (x : ParkerLoop) :
    parkerLoopMultiply x (loopInverse x) = loopOne := by
  rw [loopInverse, parkerLoopMultiply_sign_right, parkerLoopMultiply_square]
  apply Prod.ext
  · rfl
  · exact bit_add_self _

private theorem triple_repeat_left (x y : golay) :
    parkerTripleIntersection x x y = 0 := by
  rw [parkerTripleIntersection_cycle, parkerTripleIntersection_repeat]

@[simp] theorem loopInverse_mul_left (x y : ParkerLoop) :
    parkerLoopMultiply (loopInverse x) (parkerLoopMultiply x y) = y := by
  have h := parkerLoopMultiply_associator (loopInverse x) x y
  change parkerLoopMultiply (parkerLoopMultiply (loopInverse x) x) y =
    parkerSign (parkerTripleIntersection x.1 x.1 y.1)
      (parkerLoopMultiply (loopInverse x) (parkerLoopMultiply x y)) at h
  rw [triple_repeat_left, parkerSign_zero, loopInverse_mul] at h
  exact h.symm.trans (parkerLoopMultiply_one_left y)

@[simp] theorem loopInverse_mul_right (x y : ParkerLoop) :
    parkerLoopMultiply (parkerLoopMultiply y x) (loopInverse x) = y := by
  have h := parkerLoopMultiply_associator y x (loopInverse x)
  change parkerLoopMultiply (parkerLoopMultiply y x) (loopInverse x) =
    parkerSign (parkerTripleIntersection y.1 x.1 x.1)
      (parkerLoopMultiply y (parkerLoopMultiply x (loopInverse x))) at h
  rw [parkerTripleIntersection_repeat, parkerSign_zero, mul_loopInverse] at h
  exact h.trans (parkerLoopMultiply_one_right y)

/-- Left translation by a loop element. -/
def loopLeft (d : ParkerLoop) : Equiv.Perm ParkerLoop where
  toFun := parkerLoopMultiply d
  invFun := parkerLoopMultiply (loopInverse d)
  left_inv := loopInverse_mul_left d
  right_inv x := by
    simpa only [loopInverse_inverse] using loopInverse_mul_left (loopInverse d) x

/-- Right translation by a loop element. -/
def loopRight (d : ParkerLoop) : Equiv.Perm ParkerLoop where
  toFun x := parkerLoopMultiply x d
  invFun x := parkerLoopMultiply x (loopInverse d)
  left_inv := loopInverse_mul_right d
  right_inv x := by
    simpa only [loopInverse_inverse] using loopInverse_mul_right (loopInverse d) x

/-- Inversion is an involutive permutation of the Parker loop. -/
def loopInverseEquiv : Equiv.Perm ParkerLoop where
  toFun := loopInverse
  invFun := loopInverse
  left_inv := loopInverse_inverse
  right_inv := loopInverse_inverse

/-- The absorbing zero adjoined in Section 14. -/
abbrev LoopZero := Option ParkerLoop

/-- Ordered triples from the loop with its adjoined zero. -/
abbrev Triple := LoopZero × LoopZero × LoopZero

def leftZero (d : ParkerLoop) : Equiv.Perm LoopZero := Equiv.optionCongr (loopLeft d)
def rightZero (d : ParkerLoop) : Equiv.Perm LoopZero := Equiv.optionCongr (loopRight d)
def inverseZero : Equiv.Perm LoopZero := Equiv.optionCongr loopInverseEquiv

@[simp] theorem leftZero_none (d : ParkerLoop) : leftZero d none = none := rfl
@[simp] theorem rightZero_none (d : ParkerLoop) : rightZero d none = none := rfl
@[simp] theorem inverseZero_none : inverseZero none = none := rfl

@[simp] theorem leftZero_some (d x : ParkerLoop) :
    leftZero d (some x) = some (parkerLoopMultiply d x) := rfl

@[simp] theorem rightZero_some (d x : ParkerLoop) :
    rightZero d (some x) = some (parkerLoopMultiply x d) := rfl

@[simp] theorem inverseZero_some (x : ParkerLoop) :
    inverseZero (some x) = some (loopInverse x) := rfl

@[simp] theorem leftZero_one (a : LoopZero) : leftZero loopOne a = a := by
  cases a with
  | none => rfl
  | some x => exact congrArg some (parkerLoopMultiply_one_left x)

@[simp] theorem rightZero_one (a : LoopZero) : rightZero loopOne a = a := by
  cases a with
  | none => rfl
  | some x => exact congrArg some (parkerLoopMultiply_one_right x)

@[simp] theorem inverseZero_inverse (a : LoopZero) : inverseZero (inverseZero a) = a :=
  loopInverseEquiv.optionCongr.left_inv a

@[simp] theorem loopPi_mul (x : ParkerLoop) :
    parkerLoopMultiply loopPi x = parkerSign 1 x := by
  change parkerLoopMultiply (parkerSign 1 loopOne) x = _
  rw [parkerLoopMultiply_sign_left, loopOne, parkerLoopMultiply_one_left]

@[simp] theorem mul_loopPi (x : ParkerLoop) :
    parkerLoopMultiply x loopPi = parkerSign 1 x := by
  change parkerLoopMultiply x (parkerSign 1 loopOne) = _
  rw [parkerLoopMultiply_sign_right, loopOne, parkerLoopMultiply_one_right]

/-- The central sign involution, extended to fix the adjoined zero. -/
def signZero : Equiv.Perm LoopZero := leftZero loopPi

@[simp] theorem signZero_none : signZero none = none := rfl

@[simp] theorem signZero_some (x : ParkerLoop) :
    signZero (some x) = some (parkerSign 1 x) := by
  exact congrArg some (loopPi_mul x)

@[simp] theorem rightZero_pi (a : LoopZero) : rightZero loopPi a = signZero a := by
  cases a with
  | none => rfl
  | some x => simp [signZero]

@[simp] theorem leftZero_pi (a : LoopZero) : leftZero loopPi a = signZero a := rfl

@[simp] theorem signZero_signZero (a : LoopZero) : signZero (signZero a) = a := by
  cases a with
  | none => rfl
  | some x => simp [parkerSign_add]

theorem parkerLoop_card : Nat.card ParkerLoop = 8192 := by
  rw [Nat.card_prod, golay_card]
  norm_num [ParkerBit]

end Sporadic.Monster.Construction.TrialitySpin
