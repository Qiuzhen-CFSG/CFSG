module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.ZMod.Basic

/-!
# A concrete binary model for the proposed J₄ local quotient action

The two matrices below are the ATLAS representation `3M22d2G1-f2r12B0`.
Their inverses are checked in Lean, and `actionGroup` is their literal
generated subgroup of GL₁₂(2). No recognition, normalizer result, or
identification with the J₄ two-core action is asserted here.

The intended comparison is with the action on Q/Z(Q), where Q = O₂(C)
and C is the centralizer of the first certified J₄ generator. GLS3,
Table 5.3i, printed p.270 (`refs/KGroup/GLS3/Chapter5(sec3-).tex`), gives
the relevant local shape. The comparison and the normalizer calculation
are separate proof obligations.

Data source: the online ATLAS of Finite Group Representations,
R. A. Wilson, S. J. Nickerson and J. N. Bray:
https://brauer.maths.qmul.ac.uk/Atlas/v3/matrep/3M22d2G1-f2r12B0/
The original MeatAxe files and their hashes are retained in `LinearModel/source/`.
Bit j of each packed row is column j, starting at zero. There is no
transpose or basis change. The inverse of the second matrix was computed
over GF(2); both inverse identities below are kernel checked.
-/

@[expose] public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

/-- The ambient matrix algebra of the proposed quotient action. -/
abbrev Matrix12 := Matrix (Fin 12) (Fin 12) (ZMod 2)

/-- Decode binary rows, with column zero in the least significant bit. -/
def fromRows (rows : Fin 12 → ℕ) : Matrix12 :=
  fun i j => if (rows i).testBit j.val then 1 else 0

/-- The ATLAS generator named C. -/
def matrixC : Matrix12 := fromRows
  ![2, 1, 7, 32, 64, 8, 16, 512, 1024, 128, 256, 3453]

/-- The ATLAS generator named D. -/
def matrixD : Matrix12 := fromRows
  ![4, 8, 16, 2, 31, 128, 256, 778, 2048, 2976, 1639, 2666]

/-- An explicit inverse for D. -/
def matrixDInv : Matrix12 := fromRows
  ![31, 8, 1, 2, 4, 938, 2666, 32, 64, 202, 3356, 256]

theorem matrixC_mul_self : matrixC * matrixC = 1 := by decide +kernel

theorem matrixD_mul_inv : matrixD * matrixDInv = 1 := by decide +kernel

theorem matrixD_inv_mul : matrixDInv * matrixD = 1 := by decide +kernel

/-- The first generator as a certified matrix unit. -/
def unitC : Matrix12ˣ where
  val := matrixC
  inv := matrixC
  val_inv := matrixC_mul_self
  inv_val := matrixC_mul_self

/-- The second generator as a certified matrix unit. -/
def unitD : Matrix12ˣ where
  val := matrixD
  inv := matrixDInv
  val_inv := matrixD_mul_inv
  inv_val := matrixD_inv_mul

@[simp] theorem coe_unitC : (unitC : Matrix12) = matrixC := rfl

@[simp] theorem coe_unitD : (unitD : Matrix12) = matrixD := rfl

/-- The literal ATLAS matrix subgroup, without a recognition assumption. -/
def actionGroup : Subgroup Matrix12ˣ := Subgroup.closure {unitC, unitD}

theorem unitC_mem_actionGroup : unitC ∈ actionGroup :=
  Subgroup.subset_closure (Or.inl rfl)

theorem unitD_mem_actionGroup : unitD ∈ actionGroup :=
  Subgroup.subset_closure (Or.inr rfl)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
