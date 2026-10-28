module

public import Theory.Mathieu.M22.Properties.EvenLocalGeometry
public import Mathlib.Data.Fin.VecNotation

/-!
# Three elements of the marked M₂₂ Sylow subgroup

These are the degree-22 permutations used in `Properties.SylowPointwise.Innerness`.
Their preservation of the Witt design, parity, and membership in the pair–partition
intersection are checked independently here, providing a narrow reusable boundary
for the four-group calculation. No generation claim is needed at this stage.

Source context: Aschbacher–Smith 15.3.43, printed p.1140; GLS3 Table 5.3c.
-/

@[expose] public section
namespace Sporadic.Mathieu.M22FourNormalizers.FixedSylow
open Subgroup M22ValueBound.Concrete
open scoped Pointwise
set_option maxRecDepth 100000

def generatorTable : Fin 3 → Fin 22 → Fin 22 :=
  ![![6, 2, 1, 3, 9, 11, 16, 8, 5, 19, 10, 7, 4, 15, 13, 17, 21, 14, 20, 12, 18, 0],
    ![0, 2, 1, 3, 5, 4, 21, 19, 9, 8, 10, 12, 11, 13, 15, 14, 16, 17, 20, 7, 18, 6],
    ![0, 1, 2, 18, 7, 6, 5, 4, 8, 9, 20, 16, 13, 12, 19, 21, 11, 17, 3, 14, 10, 15]]

def generatorInverseTable : Fin 3 → Fin 22 → Fin 22 :=
  ![![21, 2, 1, 3, 12, 8, 0, 11, 7, 4, 10, 5, 19, 14, 17, 13, 6, 15, 20, 9, 18, 16],
    ![0, 2, 1, 3, 5, 4, 21, 19, 9, 8, 10, 12, 11, 13, 15, 14, 16, 17, 20, 7, 18, 6],
    ![0, 1, 2, 18, 7, 6, 5, 4, 8, 9, 20, 16, 13, 12, 19, 21, 11, 17, 3, 14, 10, 15]]

theorem generator_leftInverse : ∀ (i : Fin 3) (x : Fin 22),
    generatorInverseTable i (generatorTable i x) = x := by decide +kernel

theorem generator_rightInverse : ∀ (i : Fin 3) (x : Fin 22),
    generatorTable i (generatorInverseTable i x) = x := by decide +kernel

def generatorPerm (i : Fin 3) : Equiv.Perm (Fin 22) where
  toFun := generatorTable i
  invFun := generatorInverseTable i
  left_inv := generator_leftInverse i
  right_inv := generator_rightInverse i

def blockIndex : Fin 3 → Fin 77 → Fin 77 :=
  ![![0, 3, 4, 2, 1, 22, 21, 24, 23, 33, 26, 31, 34, 29, 28, 32, 25, 30, 35, 27, 36, 7, 8, 5, 6, 9, 18, 19, 14, 17, 13, 11, 20, 16, 12, 10, 15, 46, 47, 38, 41, 45, 48, 39, 40, 44, 37, 43, 42, 75, 67, 72, 62, 60, 52, 59, 69, 54, 53, 68, 61, 58, 57, 56, 76, 66, 49, 71, 70, 73, 55, 74, 64, 63, 50, 65, 51],
    ![0, 2, 1, 3, 4, 22, 21, 24, 23, 25, 29, 28, 27, 26, 31, 36, 33, 35, 30, 34, 32, 6, 5, 8, 7, 9, 13, 12, 11, 10, 18, 14, 20, 16, 19, 17, 15, 37, 40, 41, 38, 39, 42, 45, 47, 43, 46, 44, 48, 49, 50, 64, 60, 62, 61, 59, 63, 58, 57, 55, 52, 54, 53, 56, 51, 65, 75, 74, 70, 73, 68, 71, 72, 69, 67, 66, 76],
    ![0, 1, 2, 3, 4, 16, 15, 9, 20, 7, 12, 17, 10, 14, 13, 6, 5, 11, 19, 18, 8, 28, 31, 27, 34, 30, 33, 23, 21, 32, 25, 22, 29, 26, 24, 36, 35, 51, 69, 45, 40, 68, 64, 63, 55, 39, 72, 47, 76, 58, 65, 37, 60, 53, 54, 44, 70, 71, 49, 59, 52, 66, 67, 43, 42, 50, 61, 62, 41, 38, 56, 57, 46, 73, 74, 75, 48]]

theorem generator_mem (i : Fin 3) : generatorPerm i ∈ M22 := by
  constructor
  · change generatorPerm i ∈ m22WittDesign.aut
    rw [Theory.GroupTheory.SteinerSystem.mem_aut_iff]
    have hi : ∀ i : Fin 3, Finset.univ.image (blockIndex i) = Finset.univ := by
      decide +kernel
    have hb : ∀ (i : Fin 3) (j : Fin 77) (x : Fin 22),
        (m22BlockMask j).testBit ((generatorPerm i).symm x).val =
          (m22BlockMask (blockIndex i j)).testBit x.val := by
      decide +kernel
    have he := m22_blocks_smul_of_index (generatorPerm i) (blockIndex i) (hi i)
      (fun j => m22Perm_smul_blockAt_of_bits _ _ _ (hb i j))
    have hs := congrArg (fun s : Finset (Finset (Fin 22)) =>
      (s : Set (Finset (Fin 22)))) he
    simpa only [m22WittDesign, Theory.GroupTheory.SteinerSystem.ofPairwiseIntersection_blocks,
      Finset.coe_smul_finset] using hs
  · change generatorPerm i ∈ alternatingGroup (Fin 22)
    fin_cases i
    · change generatorPerm 0 ∈ alternatingGroup (Fin 22)
      have he : generatorPerm 0 = List.formPerm [0, 6, 16, 21] *
    List.formPerm [1, 2] *
    List.formPerm [4, 9, 19, 12] *
    List.formPerm [5, 11, 7, 8] *
    List.formPerm [13, 15, 17, 14] *
    List.formPerm [18, 20] := by decide +kernel
      rw [he, Equiv.Perm.mem_alternatingGroup]
      simp [List.formPerm, Equiv.Perm.sign_swap']
    · change generatorPerm 1 ∈ alternatingGroup (Fin 22)
      have he : generatorPerm 1 = List.formPerm [1, 2] *
    List.formPerm [4, 5] *
    List.formPerm [6, 21] *
    List.formPerm [7, 19] *
    List.formPerm [8, 9] *
    List.formPerm [11, 12] *
    List.formPerm [14, 15] *
    List.formPerm [18, 20] := by decide +kernel
      rw [he, Equiv.Perm.mem_alternatingGroup]
      simp [List.formPerm, Equiv.Perm.sign_swap']
    · change generatorPerm 2 ∈ alternatingGroup (Fin 22)
      have he : generatorPerm 2 = List.formPerm [3, 18] *
    List.formPerm [4, 7] *
    List.formPerm [5, 6] *
    List.formPerm [10, 20] *
    List.formPerm [11, 16] *
    List.formPerm [12, 13] *
    List.formPerm [14, 19] *
    List.formPerm [15, 21] := by decide +kernel
      rw [he, Equiv.Perm.mem_alternatingGroup]
      simp [List.formPerm, Equiv.Perm.sign_swap']

noncomputable def generator (i : Fin 3) : M22 :=
  ⟨generatorPerm i, generator_mem i⟩

theorem generator_mem_standard (i : Fin 3) :
    generator i ∈ M22EvenGeometry.sylow := by
  change generator i ∈ first ⊓ second
  constructor
  · change generatorPerm i • m22Pair12 = m22Pair12
    revert i
    decide +kernel
  · change generatorPerm i • hexadPartition = hexadPartition
    revert i
    decide +kernel

end Sporadic.Mathieu.M22FourNormalizers.FixedSylow
