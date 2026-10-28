module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.Coordinates
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.Dimensions
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.Conjugacy

/-!
# The subgroups of the four-dimensional binary coordinate group

A finite certificate lists the 67 subspaces of `C₂⁴`. Completeness is proved by
adjoining one vector at a time: each listed subspace and its translate have a
listed union. Thus the certificate covers arbitrary subgroups, including zero.
All finite identities are checked by the kernel, only inside the sixteen-element
coordinate group, identified with `D` by `binaryEquivD`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition B.3.2, printed pp. 83–84.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.Offenders.Eight.DBounds
open Representation.BinaryOffender BinaryPermutation

/-- Binary encoding of the actual four swap coordinates. -/
def vectorEquiv : Fin 16 ≃ BinaryFour :=
  (finFunctionFinEquiv (m := 2) (n := 4)).symm.trans Multiplicative.ofAdd

/-- Addition of binary words, encoded by exclusive or. -/
def addWord (x y : Fin 16) : Fin 16 := ⟨Nat.xor x.val y.val % 16, Nat.mod_lt _ (by decide)⟩

theorem vector_add (x y : Fin 16) :
    vectorEquiv (addWord x y) = vectorEquiv x * vectorEquiv y := by
  revert x y
  decide +kernel

theorem vector_zero : vectorEquiv 0 = 1 := by decide +kernel

theorem vector_inv (x : BinaryFour) : x⁻¹ = x := by
  revert x
  decide +kernel

/-- The member sets, sorted by dimension and then lexicographically. -/
def members : Fin 67 → Finset (Fin 16) := ![
  {0},
  {0, 1},
  {0, 2},
  {0, 3},
  {0, 4},
  {0, 5},
  {0, 6},
  {0, 7},
  {0, 8},
  {0, 9},
  {0, 10},
  {0, 11},
  {0, 12},
  {0, 13},
  {0, 14},
  {0, 15},
  {0, 1, 2, 3},
  {0, 1, 4, 5},
  {0, 1, 6, 7},
  {0, 1, 8, 9},
  {0, 1, 10, 11},
  {0, 1, 12, 13},
  {0, 1, 14, 15},
  {0, 2, 4, 6},
  {0, 2, 5, 7},
  {0, 2, 8, 10},
  {0, 2, 9, 11},
  {0, 2, 12, 14},
  {0, 2, 13, 15},
  {0, 3, 4, 7},
  {0, 3, 5, 6},
  {0, 3, 8, 11},
  {0, 3, 9, 10},
  {0, 3, 12, 15},
  {0, 3, 13, 14},
  {0, 4, 8, 12},
  {0, 4, 9, 13},
  {0, 4, 10, 14},
  {0, 4, 11, 15},
  {0, 5, 8, 13},
  {0, 5, 9, 12},
  {0, 5, 10, 15},
  {0, 5, 11, 14},
  {0, 6, 8, 14},
  {0, 6, 9, 15},
  {0, 6, 10, 12},
  {0, 6, 11, 13},
  {0, 7, 8, 15},
  {0, 7, 9, 14},
  {0, 7, 10, 13},
  {0, 7, 11, 12},
  {0, 1, 2, 3, 4, 5, 6, 7},
  {0, 1, 2, 3, 8, 9, 10, 11},
  {0, 1, 2, 3, 12, 13, 14, 15},
  {0, 1, 4, 5, 8, 9, 12, 13},
  {0, 1, 4, 5, 10, 11, 14, 15},
  {0, 1, 6, 7, 8, 9, 14, 15},
  {0, 1, 6, 7, 10, 11, 12, 13},
  {0, 2, 4, 6, 8, 10, 12, 14},
  {0, 2, 4, 6, 9, 11, 13, 15},
  {0, 2, 5, 7, 8, 10, 13, 15},
  {0, 2, 5, 7, 9, 11, 12, 14},
  {0, 3, 4, 7, 8, 11, 12, 15},
  {0, 3, 4, 7, 9, 10, 13, 14},
  {0, 3, 5, 6, 8, 11, 13, 14},
  {0, 3, 5, 6, 9, 10, 12, 15},
  {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}]

/-- Index of the subspace obtained by adjoining one vector. -/
def adjoinIndex : Fin 67 → Fin 16 → Fin 67 := ![
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
  ![1, 1, 16, 16, 17, 17, 18, 18, 19, 19, 20, 20, 21, 21, 22, 22],
  ![2, 16, 2, 16, 23, 24, 23, 24, 25, 26, 25, 26, 27, 28, 27, 28],
  ![3, 16, 16, 3, 29, 30, 30, 29, 31, 32, 32, 31, 33, 34, 34, 33],
  ![4, 17, 23, 29, 4, 17, 23, 29, 35, 36, 37, 38, 35, 36, 37, 38],
  ![5, 17, 24, 30, 17, 5, 30, 24, 39, 40, 41, 42, 40, 39, 42, 41],
  ![6, 18, 23, 30, 23, 30, 6, 18, 43, 44, 45, 46, 45, 46, 43, 44],
  ![7, 18, 24, 29, 29, 24, 18, 7, 47, 48, 49, 50, 50, 49, 48, 47],
  ![8, 19, 25, 31, 35, 39, 43, 47, 8, 19, 25, 31, 35, 39, 43, 47],
  ![9, 19, 26, 32, 36, 40, 44, 48, 19, 9, 32, 26, 40, 36, 48, 44],
  ![10, 20, 25, 32, 37, 41, 45, 49, 25, 32, 10, 20, 45, 49, 37, 41],
  ![11, 20, 26, 31, 38, 42, 46, 50, 31, 26, 20, 11, 50, 46, 42, 38],
  ![12, 21, 27, 33, 35, 40, 45, 50, 35, 40, 45, 50, 12, 21, 27, 33],
  ![13, 21, 28, 34, 36, 39, 46, 49, 39, 36, 49, 46, 21, 13, 34, 28],
  ![14, 22, 27, 34, 37, 42, 43, 48, 43, 48, 37, 42, 27, 34, 14, 22],
  ![15, 22, 28, 33, 38, 41, 44, 47, 47, 44, 41, 38, 33, 28, 22, 15],
  ![16, 16, 16, 16, 51, 51, 51, 51, 52, 52, 52, 52, 53, 53, 53, 53],
  ![17, 17, 51, 51, 17, 17, 51, 51, 54, 54, 55, 55, 54, 54, 55, 55],
  ![18, 18, 51, 51, 51, 51, 18, 18, 56, 56, 57, 57, 57, 57, 56, 56],
  ![19, 19, 52, 52, 54, 54, 56, 56, 19, 19, 52, 52, 54, 54, 56, 56],
  ![20, 20, 52, 52, 55, 55, 57, 57, 52, 52, 20, 20, 57, 57, 55, 55],
  ![21, 21, 53, 53, 54, 54, 57, 57, 54, 54, 57, 57, 21, 21, 53, 53],
  ![22, 22, 53, 53, 55, 55, 56, 56, 56, 56, 55, 55, 53, 53, 22, 22],
  ![23, 51, 23, 51, 23, 51, 23, 51, 58, 59, 58, 59, 58, 59, 58, 59],
  ![24, 51, 24, 51, 51, 24, 51, 24, 60, 61, 60, 61, 61, 60, 61, 60],
  ![25, 52, 25, 52, 58, 60, 58, 60, 25, 52, 25, 52, 58, 60, 58, 60],
  ![26, 52, 26, 52, 59, 61, 59, 61, 52, 26, 52, 26, 61, 59, 61, 59],
  ![27, 53, 27, 53, 58, 61, 58, 61, 58, 61, 58, 61, 27, 53, 27, 53],
  ![28, 53, 28, 53, 59, 60, 59, 60, 60, 59, 60, 59, 53, 28, 53, 28],
  ![29, 51, 51, 29, 29, 51, 51, 29, 62, 63, 63, 62, 62, 63, 63, 62],
  ![30, 51, 51, 30, 51, 30, 30, 51, 64, 65, 65, 64, 65, 64, 64, 65],
  ![31, 52, 52, 31, 62, 64, 64, 62, 31, 52, 52, 31, 62, 64, 64, 62],
  ![32, 52, 52, 32, 63, 65, 65, 63, 52, 32, 32, 52, 65, 63, 63, 65],
  ![33, 53, 53, 33, 62, 65, 65, 62, 62, 65, 65, 62, 33, 53, 53, 33],
  ![34, 53, 53, 34, 63, 64, 64, 63, 64, 63, 63, 64, 53, 34, 34, 53],
  ![35, 54, 58, 62, 35, 54, 58, 62, 35, 54, 58, 62, 35, 54, 58, 62],
  ![36, 54, 59, 63, 36, 54, 59, 63, 54, 36, 63, 59, 54, 36, 63, 59],
  ![37, 55, 58, 63, 37, 55, 58, 63, 58, 63, 37, 55, 58, 63, 37, 55],
  ![38, 55, 59, 62, 38, 55, 59, 62, 62, 59, 55, 38, 62, 59, 55, 38],
  ![39, 54, 60, 64, 54, 39, 64, 60, 39, 54, 60, 64, 54, 39, 64, 60],
  ![40, 54, 61, 65, 54, 40, 65, 61, 54, 40, 65, 61, 40, 54, 61, 65],
  ![41, 55, 60, 65, 55, 41, 65, 60, 60, 65, 41, 55, 65, 60, 55, 41],
  ![42, 55, 61, 64, 55, 42, 64, 61, 64, 61, 55, 42, 61, 64, 42, 55],
  ![43, 56, 58, 64, 58, 64, 43, 56, 43, 56, 58, 64, 58, 64, 43, 56],
  ![44, 56, 59, 65, 59, 65, 44, 56, 56, 44, 65, 59, 65, 59, 56, 44],
  ![45, 57, 58, 65, 58, 65, 45, 57, 58, 65, 45, 57, 45, 57, 58, 65],
  ![46, 57, 59, 64, 59, 64, 46, 57, 64, 59, 57, 46, 57, 46, 64, 59],
  ![47, 56, 60, 62, 62, 60, 56, 47, 47, 56, 60, 62, 62, 60, 56, 47],
  ![48, 56, 61, 63, 63, 61, 56, 48, 56, 48, 63, 61, 61, 63, 48, 56],
  ![49, 57, 60, 63, 63, 60, 57, 49, 60, 63, 49, 57, 57, 49, 63, 60],
  ![50, 57, 61, 62, 62, 61, 57, 50, 62, 61, 57, 50, 50, 57, 61, 62],
  ![51, 51, 51, 51, 51, 51, 51, 51, 66, 66, 66, 66, 66, 66, 66, 66],
  ![52, 52, 52, 52, 66, 66, 66, 66, 52, 52, 52, 52, 66, 66, 66, 66],
  ![53, 53, 53, 53, 66, 66, 66, 66, 66, 66, 66, 66, 53, 53, 53, 53],
  ![54, 54, 66, 66, 54, 54, 66, 66, 54, 54, 66, 66, 54, 54, 66, 66],
  ![55, 55, 66, 66, 55, 55, 66, 66, 66, 66, 55, 55, 66, 66, 55, 55],
  ![56, 56, 66, 66, 66, 66, 56, 56, 56, 56, 66, 66, 66, 66, 56, 56],
  ![57, 57, 66, 66, 66, 66, 57, 57, 66, 66, 57, 57, 57, 57, 66, 66],
  ![58, 66, 58, 66, 58, 66, 58, 66, 58, 66, 58, 66, 58, 66, 58, 66],
  ![59, 66, 59, 66, 59, 66, 59, 66, 66, 59, 66, 59, 66, 59, 66, 59],
  ![60, 66, 60, 66, 66, 60, 66, 60, 60, 66, 60, 66, 66, 60, 66, 60],
  ![61, 66, 61, 66, 66, 61, 66, 61, 66, 61, 66, 61, 61, 66, 61, 66],
  ![62, 66, 66, 62, 62, 66, 66, 62, 62, 66, 66, 62, 62, 66, 66, 62],
  ![63, 66, 66, 63, 63, 66, 66, 63, 66, 63, 63, 66, 66, 63, 63, 66],
  ![64, 66, 66, 64, 66, 64, 64, 66, 64, 66, 66, 64, 66, 64, 64, 66],
  ![65, 66, 66, 65, 66, 65, 65, 66, 66, 65, 65, 66, 65, 66, 66, 65],
  ![66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66]]

theorem zero_mem (i : Fin 67) : (0 : Fin 16) ∈ members i := by
  revert i
  decide +kernel

theorem add_mem (i : Fin 67) (x y : Fin 16)
    (hx : x ∈ members i) (hy : y ∈ members i) : addWord x y ∈ members i := by
  revert i x y
  decide +kernel

theorem members_adjoin (i : Fin 67) (x : Fin 16) :
    members (adjoinIndex i x) = members i ∪ (members i).image (addWord x) := by
  revert i x
  decide +kernel

/-- Each member set is a subgroup of the actual binary coordinate group. -/
def binaryGroup (i : Fin 67) : Subgroup BinaryFour where
  carrier := {x | vectorEquiv.symm x ∈ members i}
  one_mem' := by
    change vectorEquiv.symm 1 ∈ members i
    rw [← vector_zero, Equiv.symm_apply_apply]
    exact zero_mem i
  mul_mem' := by
    intro x y hx hy
    change vectorEquiv.symm (x * y) ∈ members i
    rw [← vectorEquiv.apply_symm_apply x, ← vectorEquiv.apply_symm_apply y,
      ← vector_add, Equiv.symm_apply_apply]
    exact add_mem i _ _ hx hy
  inv_mem' := by
    intro x hx
    simpa only [vector_inv] using hx

@[simp] theorem vector_mem (i : Fin 67) (x : Fin 16) :
    vectorEquiv x ∈ binaryGroup i ↔ x ∈ members i := by
  change vectorEquiv.symm (vectorEquiv x) ∈ members i ↔ _
  rw [Equiv.symm_apply_apply]

/-- Every binary subgroup occurs: the proof uses closure under adjoining vectors. -/
theorem binaryGroup_exhaustive (S : Subgroup BinaryFour) : ∃ i, binaryGroup i = S := by
  classical
  have haux (s : Finset BinaryFour) (hs : ∀ x ∈ s, x ∈ S) :
      ∃ i, (∀ x ∈ s, x ∈ binaryGroup i) ∧ binaryGroup i ≤ S := by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨0, by simp, ?_⟩
      intro x hx
      have he : vectorEquiv.symm x = 0 := by
        simpa [binaryGroup, members] using hx
      have : x = 1 := by
        rw [← vectorEquiv.apply_symm_apply x, he, vector_zero]
      simpa only [this] using S.one_mem
    | @insert x s hx ih =>
      obtain ⟨i, hi, hiS⟩ := ih (fun y hy => hs y (Finset.mem_insert_of_mem hy))
      refine ⟨adjoinIndex i (vectorEquiv.symm x), ?_, ?_⟩
      · intro y hy
        change vectorEquiv.symm y ∈ members _
        rw [members_adjoin]
        rcases Finset.mem_insert.mp hy with rfl | hy
        · apply Finset.mem_union_right
          refine Finset.mem_image.mpr ⟨0, zero_mem i, ?_⟩
          apply vectorEquiv.injective
          rw [vector_add, vector_zero, mul_one]
        · exact Finset.mem_union_left _ (hi y hy)
      · intro y hy
        change vectorEquiv.symm y ∈ members _ at hy
        rw [members_adjoin, Finset.mem_union, Finset.mem_image] at hy
        rcases hy with hy | ⟨z, hz, he⟩
        · exact hiS hy
        · have he' : y = x * vectorEquiv z := by
            rw [← vectorEquiv.apply_symm_apply y, ← he, vector_add,
              vectorEquiv.apply_symm_apply]
          rw [he']
          exact S.mul_mem (hs x (Finset.mem_insert_self _ _)) (hiS ((vector_mem i z).mpr hz))
  obtain ⟨i, hi, hiS⟩ := haux (Finset.univ.filter (· ∈ S)) (by simp)
  exact ⟨i, le_antisymm hiS (fun x hx => hi x (by simpa using hx))⟩

end CFSG.Quasithin.ChapterB.Offenders.Eight.DBounds
