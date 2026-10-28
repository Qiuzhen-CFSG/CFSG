module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.ZMod.Basic

/-!
# Nonsingularity of the proposed max2 commutator form

The twelve noncentral seed conjugates in `kernel_candidate.json` give this
candidate binary commutator matrix, after dropping the distinguished central
coordinate. An explicit inverse is checked in the Lean kernel. Thus a row
orthogonal to all twelve rows is zero.

This is a numerical certificate only: a consumer must prove that its actual
generators have these commutators. The original witnesses are preserved in
`Scratch/J4TwoCoreControl/` of workspace
`cbdf19d7b3214f02bfdf6de5be01fb63`. Generator order is the seed conjugated by
empty, y, yy, yyx, yyxy, yyxyx, yyxyy, yyxyxy, yyxyyx, yyxyxyx,
yyxyxyy, yyxyyxy, with conjugation w⁻¹*s*w. Bit zero of the original
thirteen-coordinate witness is the central involution.

Source motivation: GLS3, Table 5.3i, printed p.270. No source model
identification or extraspeciality is a premise or conclusion of this file.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreComparison.InvolutionCensus
open Matrix

/-- Candidate commutator exponents, excluding the central coordinate. -/
def commutatorForm : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0],
    ![0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1],
    ![0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1],
    ![1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0],
    ![1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0],
    ![0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0],
    ![1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1],
    ![0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0],
    ![1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1],
    ![0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0],
    ![1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0]]

/-- Explicit right inverse of the binary form. -/
def commutatorFormInverse : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ![![0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1],
    ![0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1],
    ![1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1],
    ![1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1],
    ![0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1],
    ![0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1],
    ![0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0],
    ![1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0],
    ![1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0],
    ![1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0]]

theorem commutatorForm_mul_inverse : commutatorForm * commutatorFormInverse = 1 := by
  decide +kernel

/-- Nonsingularity, in the row convention used by the saved conjugation data. -/
theorem commutatorForm_vecMul_eq_zero (v : Fin 12 → ZMod 2)
    (hv : v ᵥ* commutatorForm = 0) : v = 0 := by
  calc
    v = v ᵥ* (commutatorForm * commutatorFormInverse) := by
      rw [commutatorForm_mul_inverse, vecMul_one]
    _ = (v ᵥ* commutatorForm) ᵥ* commutatorFormInverse :=
      (vecMul_vecMul v commutatorForm commutatorFormInverse).symm
    _ = 0 := by rw [hv, zero_vecMul]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreComparison.InvolutionCensus
