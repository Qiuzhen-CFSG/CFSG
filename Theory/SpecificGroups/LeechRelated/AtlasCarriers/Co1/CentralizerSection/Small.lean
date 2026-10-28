module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co1.CentralizerSection.Matrices
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# The concrete eight-dimensional Co₁ local image

These invertible binary matrices are the restrictions of the two published
`Co1G1-max5W1` words to the split injection in `Matrices`. This module defines
their generated group independently of the 24-dimensional carrier. Identifying
this group with the elementary orthogonal group requires a generation proof;
it is not part of the definition or the inverse certificates below.

Source: ATLAS `Co1G1-max5W1`; the coordinates are recorded in `source/`.
-/

@[expose] public section
namespace Sporadic.LeechRelated.Co1.CentralizerSection
open Packed

abbrev SmallAmbient := Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)

def smallX : SmallAmbient :=
  ⟨decode Matrices.smallXRows, decode Matrices.smallXRows,
    Matrices.smallX_square, Matrices.smallX_square⟩

def smallY : SmallAmbient :=
  ⟨decode Matrices.smallYRows, decode Matrices.smallYInvRows,
    Matrices.smallY_mul_inv, Matrices.smallY_inv_mul⟩

def smallGenerated : Subgroup SmallAmbient := Subgroup.closure {smallX, smallY}

abbrev SmallCarrier := smallGenerated

end Sporadic.LeechRelated.Co1.CentralizerSection
