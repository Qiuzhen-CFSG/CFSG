module

public import Theory.Mathieu.M22.WittDesign
public import Theory.Mathieu.M22.Generators

/-!
# Computational M22 generator action on the Witt design

This module is deliberately separate from `WittDesign.lean`: the latter is
the natural `S(3,6,22)` construction and has no dependency on the ATLAS
permutation generators.  The declarations below are finite certificates that
the two standard computational generators preserve that independent design.
-/

namespace Sporadic.Mathieu

open scoped Pointwise

set_option maxRecDepth 100000

@[expose] public def m22AIndexArray : Array (Fin 77) := #[72, 74, 61, 30, 5, 4, 49, 48, 71, 63, 54, 43, 12, 22, 36, 15, 27, 67, 18, 56, 45, 66, 13, 53, 24, 25, 46, 16, 40, 60, 3, 55, 44, 73, 34, 52, 14, 62, 70, 39, 28, 41, 75, 11, 32, 20, 26, 68, 7, 6, 58, 76, 35, 23, 10, 31, 19, 57, 50, 59, 29, 2, 37, 9, 64, 65, 21, 17, 47, 69, 38, 8, 0, 33, 1, 42, 51]

public theorem m22AIndexArray_size : m22AIndexArray.size = 77 := by
  decide +kernel

public def m22AIndex (i : Fin 77) : Fin 77 :=
  m22AIndexArray[i.val]'(by
    rw [m22AIndexArray_size]
    exact i.isLt)

private theorem m22ABlock_bits (i : Fin 77) (x : Fin 22) :
    (m22BlockMask i).testBit (m22GeneratorA.symm x).val =
      (m22BlockMask (m22AIndex i)).testBit x.val := by
  revert i x
  decide +kernel

public theorem m22ABlockAt_smul (i : Fin 77) :
    m22GeneratorA • m22BlockAt i = m22BlockAt (m22AIndex i) :=
  m22Perm_smul_blockAt_of_bits _ _ _ (m22ABlock_bits i)

public theorem m22AIndex_image : Finset.univ.image m22AIndex = Finset.univ := by
  decide +kernel

@[expose] public def m22BIndexArray : Array (Fin 77) := #[55, 15, 76, 47, 28, 36, 6, 75, 65, 54, 61, 48, 35, 66, 17, 21, 50, 44, 3, 59, 11, 45, 31, 64, 20, 63, 72, 27, 39, 16, 34, 9, 68, 69, 51, 40, 0, 74, 18, 49, 57, 70, 14, 29, 42, 1, 60, 38, 24, 4, 43, 56, 67, 71, 22, 5, 30, 12, 58, 46, 19, 23, 62, 25, 10, 8, 41, 33, 53, 52, 13, 32, 26, 73, 2, 7, 37]

public theorem m22BIndexArray_size : m22BIndexArray.size = 77 := by
  decide +kernel

public def m22BIndex (i : Fin 77) : Fin 77 :=
  m22BIndexArray[i.val]'(by
    rw [m22BIndexArray_size]
    exact i.isLt)

private theorem m22BBlock_bits (i : Fin 77) (x : Fin 22) :
    (m22BlockMask i).testBit (m22GeneratorB.symm x).val =
      (m22BlockMask (m22BIndex i)).testBit x.val := by
  revert i x
  decide +kernel

public theorem m22BBlockAt_smul (i : Fin 77) :
    m22GeneratorB • m22BlockAt i = m22BlockAt (m22BIndex i) :=
  m22Perm_smul_blockAt_of_bits _ _ _ (m22BBlock_bits i)

public theorem m22BIndex_image : Finset.univ.image m22BIndex = Finset.univ := by
  decide +kernel

/-- The first ATLAS generator preserves the independently defined hexad set. -/
public theorem m22GeneratorA_blocks_smul :
    m22GeneratorA • m22Blocks = m22Blocks := by
  exact m22_blocks_smul_of_index m22GeneratorA m22AIndex m22AIndex_image m22ABlockAt_smul

/-- The second ATLAS generator preserves the independently defined hexad set. -/
public theorem m22GeneratorB_blocks_smul :
    m22GeneratorB • m22Blocks = m22Blocks := by
  exact m22_blocks_smul_of_index m22GeneratorB m22BIndex m22BIndex_image m22BBlockAt_smul

end Sporadic.Mathieu
