/-
Authors: OpenAI
-/

module

public import BenderSuzuki.PFAppendixIII.Basic
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# Projective special linear matrix groups

This file contains the concrete `PSL(2,F)` matrix-group models used by the
Peterfalvi Part II formalization.  The declarations live in the `BenderSuzuki.MatrixGroups` namespace so matrix-group models are not hidden under a Peterfalvi chapter namespace.
-/

namespace BenderSuzuki
namespace MatrixGroups

open scoped MatrixGroups
open PFAppendixIII

universe w

/-- The actual projective special linear matrix group `PSL(2,F)`. -/
@[expose] public abbrev PSL2MatrixGroup (F : Type w) [Field F] :=
  Matrix.ProjectiveSpecialLinearGroup (Fin 2) F


/-- The actual projective special linear matrix group over `GF(2^m)`. -/
@[expose] public abbrev PSL2BinaryMatrixGroup (m : ℕ) :=
  PSL2MatrixGroup (BinaryGaloisField m)

end MatrixGroups
end BenderSuzuki
