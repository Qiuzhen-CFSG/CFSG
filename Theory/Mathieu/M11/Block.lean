module

public import Theory.GroupTheory.SteinerSystem
public import Mathlib.Tactic.FinCases
public import Theory.Mathieu.M11.Generators

namespace Sporadic.Mathieu

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- The 66 W11 blocks as compact 11-bit incidence masks. -/
@[expose]
public noncomputable def m11BlockMaskArray : Array Nat := #[
  62,
  1102,
  654,
  271,
  214,
  790,
  1047,
  358,
  167,
  1574,
  583,
  1414,
  91,
  410,
  1562,
  234,
  1322,
  555,
  842,
  1163,
  626,
  1202,
  307,
  1362,
  659,
  1123,
  930,
  451,
  1730,
  1795,
  604,
  157,
  1308,
  109,
  1196,
  812,
  460,
  1549,
  1140,
  436,
  565,
  341,
  1684,
  740,
  1317,
  1221,
  1860,
  901,
  376,
  696,
  1081,
  1240,
  793,
  1640,
  425,
  713,
  1353,
  1928,
  241,
  1840,
  976,
  1617,
  1425,
  1504,
  865,
  1697
]

public theorem m11BlockMaskArray_size : m11BlockMaskArray.size = 66 := by decide +kernel

@[expose]
public noncomputable def m11BlockMask (i : Fin 66) : Nat :=
  m11BlockMaskArray[i.val]'(by rw [m11BlockMaskArray_size]; exact i.isLt)

/-- Decode a mask into the corresponding W11 block. -/
@[expose]
public noncomputable def m11BlockAt (i : Fin 66) : Finset (Fin 11) :=
  Finset.univ.filter (fun x => (m11BlockMask i &&& (1 <<< x.val)) ≠ 0)

public theorem m11BlockAt_card : ∀ i, (m11BlockAt i).card = 5 := by decide +kernel

/-- Compact bitmask certificate for intersections of distinct listed blocks. -/
public theorem m11BlockAt_inter_card_lt_four : ∀ i j : Fin 66, i ≠ j →
    (m11BlockAt i ∩ m11BlockAt j).card < 4 := by decide +kernel

@[expose]
public noncomputable def m11Blocks : Finset (Finset (Fin 11)) :=
  Finset.univ.image m11BlockAt

public theorem m11Block_card (B : Finset (Fin 11)) (hB : B ∈ m11Blocks) : B.card = 5 := by
  rw [m11Blocks] at hB
  rcases Finset.mem_image.mp hB with ⟨i, -, rfl⟩
  exact m11BlockAt_card i

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

open scoped Pointwise

/-- The block-index permutation induced by the first ATLAS generator. -/
public def m11GeneratorA_blockIndexArray : Array (Fin 66) := #[
  19, 1, 16, 14, 25, 29, 6, 28, 21, 11, 23, 9, 12, 17, 3, 15, 2, 13, 18, 0,
  27, 8, 24, 10, 22, 4, 26, 20, 7, 5, 56, 50, 37, 51, 34, 57, 53, 32, 45, 65,
  62, 61, 44, 63, 42, 38, 46, 59, 55, 54, 31, 33, 52, 36, 49, 48, 30, 35, 58, 47,
  64, 41, 40, 43, 60, 39]

public theorem m11GeneratorA_blockIndexArray_size :
    m11GeneratorA_blockIndexArray.size = 66 := by decide +kernel

public def m11GeneratorA_blockIndex (i : Fin 66) : Fin 66 :=
  m11GeneratorA_blockIndexArray[i.val]'
    (by
      rw [m11GeneratorA_blockIndexArray_size]
      exact i.isLt)

/-- Kernel-checked bitmask certificate for the 66 block images of `A`. -/
public theorem m11GeneratorA_blockAt_smul : ∀ i : Fin 66,
    m11GeneratorA • m11BlockAt i = m11BlockAt (m11GeneratorA_blockIndex i) := by decide +kernel

public theorem m11GeneratorA_blockIndex_image :
    Finset.univ.image m11GeneratorA_blockIndex = Finset.univ := by decide +kernel

/-- The block-index permutation induced by the second ATLAS generator. -/
public def m11GeneratorB_blockIndexArray : Array (Fin 66) := #[
  48, 59, 39, 22, 49, 0, 50, 20, 58, 38, 40, 21, 52, 13, 32, 60,
  23, 41, 5, 62, 30, 51, 12, 14, 31, 61, 4, 24, 42, 6, 35, 54,
  16, 64, 63, 7, 26, 44, 53, 15, 33, 17, 34, 43, 25, 65, 9, 8,
  18, 36, 56, 57, 3, 46, 27, 47, 29, 11, 55, 1, 2, 37, 19, 28, 10, 45]

public theorem m11GeneratorB_blockIndexArray_size :
    m11GeneratorB_blockIndexArray.size = 66 := by decide +kernel

public def m11GeneratorB_blockIndex (i : Fin 66) : Fin 66 :=
  m11GeneratorB_blockIndexArray[i.val]'
    (by
      rw [m11GeneratorB_blockIndexArray_size]
      exact i.isLt)

/-- Kernel-checked bitmask certificate for the 66 block images of `B`. -/
public theorem m11GeneratorB_blockAt_smul : ∀ i : Fin 66,
    m11GeneratorB • m11BlockAt i = m11BlockAt (m11GeneratorB_blockIndex i) := by decide +kernel

public theorem m11GeneratorB_blockIndex_image :
    Finset.univ.image m11GeneratorB_blockIndex = Finset.univ := by decide +kernel

private theorem m11_blocks_smul_of_index
    (g : Equiv.Perm (Fin 11)) (index : Fin 66 -> Fin 66)
    (hblock : ∀ i, g • m11BlockAt i = m11BlockAt (index i))
    (hindex : Finset.univ.image index = Finset.univ) :
    g • m11Blocks = m11Blocks := by
  rw [m11Blocks, Finset.smul_finset_def]
  simp only [Finset.image_image, Function.comp_def]
  rw [show (fun i : Fin 66 => g • m11BlockAt i) =
      (fun i => m11BlockAt (index i)) by
    funext i
    exact hblock i]
  change Finset.image (m11BlockAt ∘ index) Finset.univ = Finset.image m11BlockAt Finset.univ
  rw [← Finset.image_image, hindex]

/-- The first ATLAS generator preserves the explicit Witt block set. -/
public theorem m11GeneratorA_blocks_smul : m11GeneratorA • m11Blocks = m11Blocks :=
  m11_blocks_smul_of_index m11GeneratorA m11GeneratorA_blockIndex
    m11GeneratorA_blockAt_smul m11GeneratorA_blockIndex_image

/-- The second ATLAS generator preserves the explicit Witt block set. -/
public theorem m11GeneratorB_blocks_smul : m11GeneratorB • m11Blocks = m11Blocks :=
  m11_blocks_smul_of_index m11GeneratorB m11GeneratorB_blockIndex
    m11GeneratorB_blockAt_smul m11GeneratorB_blockIndex_image

end Sporadic.Mathieu
