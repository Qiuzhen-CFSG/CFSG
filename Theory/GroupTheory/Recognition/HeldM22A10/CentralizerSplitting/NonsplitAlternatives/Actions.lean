module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.Actions
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Matrix.Basic

/-!
# Two further binary S4-actions for the extension classification

Besides the four-coordinate permutation action and its parity twist, the
local extension problem requires two more actions. Here they are specified
by the images of the four basis vectors for each of the twenty-four quotient
permutations. The tables define actual linear actions: their multiplication
identities are checked by kernel reduction, and matrix multiplication then
proves composition on arbitrary vectors.

A column is encoded by an integer from zero to fifteen, with coordinate j
in bit j. A permutation has code 64*s(0) + 16*s(1) + 4*s(2) + s(3).
The names refer to the exploratory orbit patterns 1,1,2,12 and 1,1,2,6,6;
no orbit classification or extension comparison is assumed by the definitions.
The tables were selected from conjugation on elementary kernels in finite
extension exploration, but every asserted action law below is proved in Lean.

These are auxiliary coordinates for Huppert--Blackburn, *Finite Groups III*,
XII.1.18(b), p.314. The tables are computational choices, not tables attributed
to the source. Completeness of these four action alternatives and comparison
of their extensions with `NonsplitModels` remain separate obligations.
-/

namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives
open LocalModelDichotomy
open scoped BigOperators

/-- The base-four code of the four images of a permutation. -/
@[expose] public def permutationCode (s : SymmetricFour) : ℕ :=
  (s 0).val * 64 + (s 1).val * 16 + (s 2).val * 4 + (s 3).val

/-- Decode the binary columns of a four-dimensional linear map. -/
@[expose] public def coefficientMatrix (matrix : SymmetricFour → Fin 4 → Fin 16)
    (s : SymmetricFour) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  fun j i => (((matrix s i).val / 2 ^ j.val % 2 : ℕ) : ZMod 2)

/-- Apply the linear map decoded from its four binary columns. -/
@[expose] public def matrixActionFun (matrix : SymmetricFour → Fin 4 → Fin 16)
    (s : SymmetricFour) (v : BinaryFour) : BinaryFour :=
  Multiplicative.ofAdd ((coefficientMatrix matrix s).mulVec v.toAdd)

private theorem matrixActionFun_linear (matrix : SymmetricFour → Fin 4 → Fin 16)
    (s : SymmetricFour) (v w : BinaryFour) :
    matrixActionFun matrix s (v * w) = matrixActionFun matrix s v * matrixActionFun matrix s w :=
  congrArg Multiplicative.ofAdd (Matrix.mulVec_add _ _ _)

/-- Binary columns for each permutation in this explicit action. -/
@[expose] public def twelveOrbitColumns (s : SymmetricFour) : Fin 4 → Fin 16 :=
  match permutationCode s with
  | 27 => ![1, 2, 4, 8]
  | 30 => ![2, 1, 12, 8]
  | 39 => ![3, 2, 12, 8]
  | 45 => ![2, 3, 4, 8]
  | 54 => ![3, 1, 4, 8]
  | 57 => ![1, 3, 12, 8]
  | 75 => ![6, 13, 12, 8]
  | 78 => ![13, 6, 4, 8]
  | 99 => ![11, 13, 4, 8]
  | 108 => ![13, 11, 12, 8]
  | 114 => ![11, 6, 12, 8]
  | 120 => ![6, 11, 4, 8]
  | 135 => ![14, 7, 4, 8]
  | 141 => ![7, 14, 12, 8]
  | 147 => ![9, 7, 12, 8]
  | 156 => ![7, 9, 4, 8]
  | 177 => ![9, 14, 4, 8]
  | 180 => ![14, 9, 12, 8]
  | 198 => ![5, 15, 12, 8]
  | 201 => ![15, 5, 4, 8]
  | 210 => ![10, 15, 4, 8]
  | 216 => ![15, 10, 12, 8]
  | 225 => ![10, 5, 12, 8]
  | 228 => ![5, 10, 4, 8]
  | _ => ![1, 2, 4, 8]

private def twelveOrbitFun := matrixActionFun twelveOrbitColumns

private theorem twelveOrbit_one : ∀ v, twelveOrbitFun 1 v = v := by
  have h : coefficientMatrix twelveOrbitColumns 1 = 1 := by decide +kernel
  intro v
  change Multiplicative.ofAdd ((coefficientMatrix twelveOrbitColumns 1).mulVec v.toAdd) = v
  rw [h, Matrix.one_mulVec]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem twelveOrbit_matrix_mul : ∀ s t,
    coefficientMatrix twelveOrbitColumns (s * t) =
      coefficientMatrix twelveOrbitColumns s * coefficientMatrix twelveOrbitColumns t := by
  decide +kernel

private theorem twelveOrbit_mul (s t : SymmetricFour) (v : BinaryFour) :
    twelveOrbitFun (s * t) v = twelveOrbitFun s (twelveOrbitFun t v) := by
  change Multiplicative.ofAdd ((coefficientMatrix twelveOrbitColumns (s * t)).mulVec v.toAdd) =
    Multiplicative.ofAdd ((coefficientMatrix twelveOrbitColumns s).mulVec
      ((coefficientMatrix twelveOrbitColumns t).mulVec v.toAdd))
  rw [twelveOrbit_matrix_mul, Matrix.mulVec_mulVec]

private theorem twelveOrbit_linear : ∀ s v w,
    twelveOrbitFun s (v * w) = twelveOrbitFun s v * twelveOrbitFun s w :=
  matrixActionFun_linear twelveOrbitColumns

/-- The explicit S4-action defined by these binary columns. -/
@[expose] public def twelveOrbitAction : SymmetricFour →* MulAut BinaryFour where
  toFun s :=
    { toFun := matrixActionFun twelveOrbitColumns s
      invFun := matrixActionFun twelveOrbitColumns s⁻¹
      left_inv := fun v => by
        change twelveOrbitFun s⁻¹ (twelveOrbitFun s v) = v
        rw [← twelveOrbit_mul, inv_mul_cancel, twelveOrbit_one]
      right_inv := fun v => by
        change twelveOrbitFun s (twelveOrbitFun s⁻¹ v) = v
        rw [← twelveOrbit_mul, mul_inv_cancel, twelveOrbit_one]
      map_mul' := by exact twelveOrbit_linear s }
  map_one' := by exact MulEquiv.ext twelveOrbit_one
  map_mul' s t := by exact MulEquiv.ext (twelveOrbit_mul s t)

/-- The action has the displayed binary-matrix formula. -/
public theorem twelveOrbitAction_apply (s : SymmetricFour) (v : BinaryFour) :
    twelveOrbitAction s v = matrixActionFun twelveOrbitColumns s v := rfl

/-- Binary columns for each permutation in this explicit action. -/
@[expose] public def sixOrbitColumns (s : SymmetricFour) : Fin 4 → Fin 16 :=
  match permutationCode s with
  | 27 => ![1, 2, 4, 8]
  | 30 => ![9, 6, 4, 8]
  | 39 => ![9, 12, 10, 8]
  | 45 => ![1, 6, 10, 8]
  | 54 => ![1, 12, 14, 8]
  | 57 => ![9, 2, 14, 8]
  | 75 => ![9, 14, 4, 8]
  | 78 => ![1, 10, 4, 8]
  | 99 => ![1, 12, 6, 8]
  | 108 => ![9, 10, 6, 8]
  | 114 => ![9, 12, 2, 8]
  | 120 => ![1, 14, 2, 8]
  | 135 => ![1, 14, 10, 8]
  | 141 => ![9, 4, 10, 8]
  | 147 => ![9, 2, 6, 8]
  | 156 => ![1, 4, 6, 8]
  | 177 => ![1, 2, 12, 8]
  | 180 => ![9, 14, 12, 8]
  | 198 => ![9, 10, 14, 8]
  | 201 => ![1, 4, 14, 8]
  | 210 => ![1, 6, 2, 8]
  | 216 => ![9, 4, 2, 8]
  | 225 => ![9, 6, 12, 8]
  | 228 => ![1, 10, 12, 8]
  | _ => ![1, 2, 4, 8]

private def sixOrbitFun := matrixActionFun sixOrbitColumns

private theorem sixOrbit_one : ∀ v, sixOrbitFun 1 v = v := by
  have h : coefficientMatrix sixOrbitColumns 1 = 1 := by decide +kernel
  intro v
  change Multiplicative.ofAdd ((coefficientMatrix sixOrbitColumns 1).mulVec v.toAdd) = v
  rw [h, Matrix.one_mulVec]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem sixOrbit_matrix_mul : ∀ s t,
    coefficientMatrix sixOrbitColumns (s * t) =
      coefficientMatrix sixOrbitColumns s * coefficientMatrix sixOrbitColumns t := by
  decide +kernel

private theorem sixOrbit_mul (s t : SymmetricFour) (v : BinaryFour) :
    sixOrbitFun (s * t) v = sixOrbitFun s (sixOrbitFun t v) := by
  change Multiplicative.ofAdd ((coefficientMatrix sixOrbitColumns (s * t)).mulVec v.toAdd) =
    Multiplicative.ofAdd ((coefficientMatrix sixOrbitColumns s).mulVec
      ((coefficientMatrix sixOrbitColumns t).mulVec v.toAdd))
  rw [sixOrbit_matrix_mul, Matrix.mulVec_mulVec]

private theorem sixOrbit_linear : ∀ s v w,
    sixOrbitFun s (v * w) = sixOrbitFun s v * sixOrbitFun s w :=
  matrixActionFun_linear sixOrbitColumns

/-- The explicit S4-action defined by these binary columns. -/
@[expose] public def sixOrbitAction : SymmetricFour →* MulAut BinaryFour where
  toFun s :=
    { toFun := matrixActionFun sixOrbitColumns s
      invFun := matrixActionFun sixOrbitColumns s⁻¹
      left_inv := fun v => by
        change sixOrbitFun s⁻¹ (sixOrbitFun s v) = v
        rw [← sixOrbit_mul, inv_mul_cancel, sixOrbit_one]
      right_inv := fun v => by
        change sixOrbitFun s (sixOrbitFun s⁻¹ v) = v
        rw [← sixOrbit_mul, mul_inv_cancel, sixOrbit_one]
      map_mul' := by exact sixOrbit_linear s }
  map_one' := by exact MulEquiv.ext sixOrbit_one
  map_mul' s t := by exact MulEquiv.ext (sixOrbit_mul s t)

/-- The action has the displayed binary-matrix formula. -/
public theorem sixOrbitAction_apply (s : SymmetricFour) (v : BinaryFour) :
    sixOrbitAction s v = matrixActionFun sixOrbitColumns s v := rfl

/-- An actual change of binary basis intertwining two actions of the same S4. -/
@[expose] public def ActionEquivalent
    (α β : SymmetricFour →* MulAut BinaryFour) : Prop :=
  ∃ e : MulAut BinaryFour, ∀ (s : SymmetricFour) (v : BinaryFour),
    e (α s v) = β s (e v)

end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives
