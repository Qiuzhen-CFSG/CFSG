module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenDescentEdgeData
import Mathlib.Tactic.FinCases

/-!
# Identification of the small even descent node words

The diagnostic generator table describes the original nonzero descent nodes.
For each row we identify its numerical word indices, express the range as the
image of that finite set, and discard repetitions of the final generator.
The resulting root words are definitionally the original node generators,
including the 59 named candidates. All 600 node numbers are preserved.

Source: Shinoda (1975), (2.3), pp. 81–82; the diagnostic root-word transcription
is recorded in `SmallEvenDescentEdgeData`. No group calculation is required.
-/

namespace ReeTwo.SylowModel.SmallEvenDescentEdges

set_option maxRecDepth 10000

private theorem nodeClosure_eq_0 : nodeClosure 0 = smallEvenDescentNode 1 := by
  have hi : nodeGeneratorIndex 0 = ![371, 355, 250, 124, 116, 34, 8, 6, 3, 1] := rfl
  calc
    nodeClosure 0 = Subgroup.closure ({word 371, word 355, word 250, word 124, word 116, word 34, word 8, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 0)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 1 := rfl

private theorem nodeClosure_eq_1 : nodeClosure 1 = smallEvenDescentNode 2 := by
  have hi : nodeGeneratorIndex 1 = ![371, 355, 141, 124, 116, 34, 8, 6, 3, 1] := rfl
  calc
    nodeClosure 1 = Subgroup.closure ({word 371, word 355, word 141, word 124, word 116, word 34, word 8, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 1)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 2 := rfl

private theorem nodeClosure_eq_2 : nodeClosure 2 = smallEvenDescentNode 3 := by
  have hi : nodeGeneratorIndex 2 = ![371, 355, 348, 124, 116, 34, 8, 6, 3, 1] := rfl
  calc
    nodeClosure 2 = Subgroup.closure ({word 371, word 355, word 348, word 124, word 116, word 34, word 8, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 2)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 3 := rfl

private theorem nodeClosure_eq_3 : nodeClosure 3 = smallEvenDescentNode 4 := by
  have hi : nodeGeneratorIndex 3 = ![371, 373, 250, 124, 116, 34, 8, 6, 3, 1] := rfl
  calc
    nodeClosure 3 = Subgroup.closure ({word 371, word 373, word 250, word 124, word 116, word 34, word 8, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 3)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 1 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 4 := rfl

private theorem nodeClosure_eq_4 : nodeClosure 4 = smallEvenDescentNode 5 := by
  have hi : nodeGeneratorIndex 4 = ![371, 194, 141, 124, 116, 34, 8, 6, 3, 1] := rfl
  calc
    nodeClosure 4 = Subgroup.closure ({word 371, word 194, word 141, word 124, word 116, word 34, word 8, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 4)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 5 := rfl

private theorem nodeClosure_eq_5 : nodeClosure 5 = smallEvenDescentNode 6 := by
  have hi : nodeGeneratorIndex 5 = ![371, 373, 348, 124, 116, 34, 8, 6, 3, 1] := rfl
  calc
    nodeClosure 5 = Subgroup.closure ({word 371, word 373, word 348, word 124, word 116, word 34, word 8, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 5)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 1 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 6 := rfl

private theorem nodeClosure_eq_6 : nodeClosure 6 = smallEvenDescentNode 7 := by
  have hi : nodeGeneratorIndex 6 = ![355, 250, 141, 124, 116, 34, 8, 6, 3, 1] := rfl
  calc
    nodeClosure 6 = Subgroup.closure ({word 355, word 250, word 141, word 124, word 116, word 34, word 8, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 6)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 7 := rfl

private theorem nodeClosure_eq_7 : nodeClosure 7 = smallEvenDescentNode 8 := by
  have hi : nodeGeneratorIndex 7 = ![157, 355, 141, 124, 116, 34, 8, 6, 3, 1] := rfl
  calc
    nodeClosure 7 = Subgroup.closure ({word 157, word 355, word 141, word 124, word 116, word 34, word 8, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 7)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton]
    _ = Subgroup.closure ({root 0, rootOne ^ 2 * root 0 * root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 8 := rfl

private theorem nodeClosure_eq_8 : nodeClosure 8 = smallEvenDescentNode 9 := by
  have hi : nodeGeneratorIndex 8 = ![44, 250, 141, 124, 116, 34, 8, 6, 3, 1] := rfl
  calc
    nodeClosure 8 = Subgroup.closure ({word 44, word 250, word 141, word 124, word 116, word 34, word 8, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 8)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 9 := rfl

private theorem nodeClosure_eq_9 : nodeClosure 9 = smallEvenDescentNode 10 := by
  have hi : nodeGeneratorIndex 9 = ![157, 194, 141, 124, 116, 34, 8, 6, 3, 1] := rfl
  calc
    nodeClosure 9 = Subgroup.closure ({word 157, word 194, word 141, word 124, word 116, word 34, word 8, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 9)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton]
    _ = Subgroup.closure ({root 0, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 10 := rfl

private theorem nodeClosure_eq_10 : nodeClosure 10 = smallEvenDescentNode 11 := by
  have hi : nodeGeneratorIndex 10 = ![371, 355, 250, 124, 113, 15, 5, 3, 1, 1] := rfl
  calc
    nodeClosure 10 = Subgroup.closure ({word 371, word 355, word 250, word 124, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 10)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 11 := rfl

private theorem nodeClosure_eq_11 : nodeClosure 11 = smallEvenDescentNode 12 := by
  have hi : nodeGeneratorIndex 11 = ![371, 355, 34, 124, 113, 15, 5, 3, 1, 1] := rfl
  calc
    nodeClosure 11 = Subgroup.closure ({word 371, word 355, word 34, word 124, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 11)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 12 := rfl

private theorem nodeClosure_eq_12 : nodeClosure 12 = smallEvenDescentNode 13 := by
  have hi : nodeGeneratorIndex 12 = ![371, 355, 261, 124, 113, 15, 5, 3, 1, 1] := rfl
  calc
    nodeClosure 12 = Subgroup.closure ({word 371, word 355, word 261, word 124, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 12)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3, rootOne ^ 2 * root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 13 := rfl

private theorem nodeClosure_eq_13 : nodeClosure 13 = smallEvenDescentNode 14 := by
  have hi : nodeGeneratorIndex 13 = ![371, 359, 250, 124, 113, 15, 5, 3, 1, 1] := rfl
  calc
    nodeClosure 13 = Subgroup.closure ({word 371, word 359, word 250, word 124, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 13)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3 * root 4 * root 7 * root 8, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 14 := rfl

private theorem nodeClosure_eq_14 : nodeClosure 14 = smallEvenDescentNode 15 := by
  have hi : nodeGeneratorIndex 14 = ![371, 194, 34, 124, 113, 15, 5, 3, 1, 1] := rfl
  calc
    nodeClosure 14 = Subgroup.closure ({word 371, word 194, word 34, word 124, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 14)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 15 := rfl

private theorem nodeClosure_eq_15 : nodeClosure 15 = smallEvenDescentNode 16 := by
  have hi : nodeGeneratorIndex 15 = ![371, 359, 261, 124, 113, 15, 5, 3, 1, 1] := rfl
  calc
    nodeClosure 15 = Subgroup.closure ({word 371, word 359, word 261, word 124, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 15)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 16 := rfl

private theorem nodeClosure_eq_16 : nodeClosure 16 = smallEvenDescentNode 17 := by
  have hi : nodeGeneratorIndex 16 = ![355, 250, 34, 124, 113, 15, 5, 3, 1, 1] := rfl
  calc
    nodeClosure 16 = Subgroup.closure ({word 355, word 250, word 34, word 124, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 16)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 3, rootOne ^ 2, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 17 := rfl

private theorem nodeClosure_eq_17 : nodeClosure 17 = smallEvenDescentNode 18 := by
  have hi : nodeGeneratorIndex 17 = ![157, 355, 34, 124, 113, 15, 5, 3, 1, 1] := rfl
  calc
    nodeClosure 17 = Subgroup.closure ({word 157, word 355, word 34, word 124, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 17)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, rootOne ^ 2 * root 0 * root 3, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 18 := rfl

private theorem nodeClosure_eq_18 : nodeClosure 18 = smallEvenDescentNode 19 := by
  have hi : nodeGeneratorIndex 18 = ![44, 250, 34, 124, 113, 15, 5, 3, 1, 1] := rfl
  calc
    nodeClosure 18 = Subgroup.closure ({word 44, word 250, word 34, word 124, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 18)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 19 := rfl

private theorem nodeClosure_eq_19 : nodeClosure 19 = smallEvenDescentNode 20 := by
  have hi : nodeGeneratorIndex 19 = ![157, 194, 34, 124, 113, 15, 5, 3, 1, 1] := rfl
  calc
    nodeClosure 19 = Subgroup.closure ({word 157, word 194, word 34, word 124, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 19)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 20 := rfl

private theorem nodeClosure_eq_20 : nodeClosure 20 = smallEvenDescentNode 21 := by
  have hi : nodeGeneratorIndex 20 = ![371, 373, 124, 116, 34, 8, 6, 3, 1, 1] := rfl
  calc
    nodeClosure 20 = Subgroup.closure ({word 371, word 373, word 124, word 116, word 34, word 8, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 20)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 1 * root 5 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 21 := rfl

private theorem nodeClosure_eq_21 : nodeClosure 21 = smallEvenDescentNode 22 := by
  have hi : nodeGeneratorIndex 21 = ![355, 141, 124, 116, 34, 8, 6, 3, 1, 1] := rfl
  calc
    nodeClosure 21 = Subgroup.closure ({word 355, word 141, word 124, word 116, word 34, word 8, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 21)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 22 := rfl

private theorem nodeClosure_eq_22 : nodeClosure 22 = smallEvenDescentNode 23 := by
  have hi : nodeGeneratorIndex 22 = ![44, 141, 124, 116, 34, 8, 6, 3, 1, 1] := rfl
  calc
    nodeClosure 22 = Subgroup.closure ({word 44, word 141, word 124, word 116, word 34, word 8, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 22)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 23 := rfl

private theorem nodeClosure_eq_23 : nodeClosure 23 = smallEvenDescentNode 24 := by
  have hi : nodeGeneratorIndex 23 = ![371, 247, 124, 116, 34, 8, 6, 3, 1, 1] := rfl
  calc
    nodeClosure 23 = Subgroup.closure ({word 371, word 247, word 124, word 116, word 34, word 8, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 23)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 24 := rfl

private theorem nodeClosure_eq_24 : nodeClosure 24 = smallEvenDescentNode 25 := by
  have hi : nodeGeneratorIndex 24 = ![355, 348, 124, 116, 34, 8, 6, 3, 1, 1] := rfl
  calc
    nodeClosure 24 = Subgroup.closure ({word 355, word 348, word 124, word 116, word 34, word 8, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 24)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 3, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 25 := rfl

private theorem nodeClosure_eq_25 : nodeClosure 25 = smallEvenDescentNode 26 := by
  have hi : nodeGeneratorIndex 25 = ![220, 355, 124, 116, 34, 8, 6, 3, 1, 1] := rfl
  calc
    nodeClosure 25 = Subgroup.closure ({word 220, word 355, word 124, word 116, word 34, word 8, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 25)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 26 := rfl

private theorem nodeClosure_eq_26 : nodeClosure 26 = smallEvenDescentNode 27 := by
  have hi : nodeGeneratorIndex 26 = ![44, 348, 124, 116, 34, 8, 6, 3, 1, 1] := rfl
  calc
    nodeClosure 26 = Subgroup.closure ({word 44, word 348, word 124, word 116, word 34, word 8, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 26)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 27 := rfl

private theorem nodeClosure_eq_27 : nodeClosure 27 = smallEvenDescentNode 28 := by
  have hi : nodeGeneratorIndex 27 = ![131, 250, 124, 116, 34, 8, 6, 3, 1, 1] := rfl
  calc
    nodeClosure 27 = Subgroup.closure ({word 131, word 250, word 124, word 116, word 34, word 8, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 27)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 1 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 28 := rfl

private theorem nodeClosure_eq_28 : nodeClosure 28 = smallEvenDescentNode 29 := by
  have hi : nodeGeneratorIndex 28 = ![157, 235, 124, 116, 34, 8, 6, 3, 1, 1] := rfl
  calc
    nodeClosure 28 = Subgroup.closure ({word 157, word 235, word 124, word 116, word 34, word 8, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 28)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 29 := rfl

private theorem nodeClosure_eq_29 : nodeClosure 29 = smallEvenDescentNode 30 := by
  have hi : nodeGeneratorIndex 29 = ![194, 141, 124, 116, 34, 8, 6, 3, 1, 1] := rfl
  calc
    nodeClosure 29 = Subgroup.closure ({word 194, word 141, word 124, word 116, word 34, word 8, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 29)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 30 := rfl

private theorem nodeClosure_eq_30 : nodeClosure 30 = smallEvenDescentNode 31 := by
  have hi : nodeGeneratorIndex 30 = ![266, 141, 124, 116, 34, 8, 6, 3, 1, 1] := rfl
  calc
    nodeClosure 30 = Subgroup.closure ({word 266, word 141, word 124, word 116, word 34, word 8, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 30)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 31 := rfl

private theorem nodeClosure_eq_31 : nodeClosure 31 = smallEvenDescentNode 32 := by
  have hi : nodeGeneratorIndex 31 = ![131, 348, 124, 116, 34, 8, 6, 3, 1, 1] := rfl
  calc
    nodeClosure 31 = Subgroup.closure ({word 131, word 348, word 124, word 116, word 34, word 8, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 31)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 1 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 32 := rfl

private theorem nodeClosure_eq_32 : nodeClosure 32 = smallEvenDescentNode 33 := by
  have hi : nodeGeneratorIndex 32 = ![44, 250, 141, 18, 35, 10, 7, 2, 1, 1] := rfl
  calc
    nodeClosure 32 = Subgroup.closure ({word 44, word 250, word 141, word 18, word 35, word 10, word 7, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 32)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8, root 4 * root 7 * root 8 * root 9, root 6 * root 8, root 7 * root 8 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 33 := rfl

private theorem nodeClosure_eq_33 : nodeClosure 33 = smallEvenDescentNode 34 := by
  have hi : nodeGeneratorIndex 33 = ![90, 250, 141, 18, 35, 10, 7, 2, 1, 1] := rfl
  calc
    nodeClosure 33 = Subgroup.closure ({word 90, word 250, word 141, word 18, word 35, word 10, word 7, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 33)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8, root 4 * root 7 * root 8 * root 9, root 6 * root 8, root 7 * root 8 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 34 := rfl

private theorem nodeClosure_eq_34 : nodeClosure 34 = smallEvenDescentNode 35 := by
  have hi : nodeGeneratorIndex 34 = ![157, 194, 141, 116, 27, 15, 5, 3, 1, 1] := rfl
  calc
    nodeClosure 34 = Subgroup.closure ({word 157, word 194, word 141, word 116, word 27, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 34)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 35 := rfl

private theorem nodeClosure_eq_35 : nodeClosure 35 = smallEvenDescentNode 36 := by
  have hi : nodeGeneratorIndex 35 = ![157, 194, 141, 34, 27, 15, 5, 3, 1, 1] := rfl
  calc
    nodeClosure 35 = Subgroup.closure ({word 157, word 194, word 141, word 34, word 27, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 35)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 36 := rfl

private theorem nodeClosure_eq_36 : nodeClosure 36 = smallEvenDescentNode 37 := by
  have hi : nodeGeneratorIndex 36 = ![157, 194, 141, 103, 27, 15, 5, 3, 1, 1] := rfl
  calc
    nodeClosure 36 = Subgroup.closure ({word 157, word 194, word 141, word 103, word 27, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 36)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 8, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 37 := rfl

private theorem nodeClosure_eq_37 : nodeClosure 37 = smallEvenDescentNode 38 := by
  have hi : nodeGeneratorIndex 37 = ![157, 182, 141, 116, 27, 15, 5, 3, 1, 1] := rfl
  calc
    nodeClosure 37 = Subgroup.closure ({word 157, word 182, word 141, word 116, word 27, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 37)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 2 * root 5 * root 6 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 38 := rfl

private theorem nodeClosure_eq_38 : nodeClosure 38 = smallEvenDescentNode 39 := by
  have hi : nodeGeneratorIndex 38 = ![157, 169, 141, 34, 27, 15, 5, 3, 1, 1] := rfl
  calc
    nodeClosure 38 = Subgroup.closure ({word 157, word 169, word 141, word 34, word 27, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 38)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 3 * root 5 * root 6 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 39 := rfl

private theorem nodeClosure_eq_39 : nodeClosure 39 = smallEvenDescentNode 40 := by
  have hi : nodeGeneratorIndex 39 = ![157, 182, 141, 103, 27, 15, 5, 3, 1, 1] := rfl
  calc
    nodeClosure 39 = Subgroup.closure ({word 157, word 182, word 141, word 103, word 27, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 39)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 2 * root 5 * root 6 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 8, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 40 := rfl

private theorem nodeClosure_eq_40 : nodeClosure 40 = smallEvenDescentNode 41 := by
  have hi : nodeGeneratorIndex 40 = ![371, 355, 250, 124, 113, 3, 5, 1, 1, 1] := rfl
  calc
    nodeClosure 40 = Subgroup.closure ({word 371, word 355, word 250, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 40)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 41 := rfl

private theorem nodeClosure_eq_41 : nodeClosure 41 = smallEvenDescentNode 42 := by
  have hi : nodeGeneratorIndex 41 = ![371, 355, 15, 124, 113, 3, 5, 1, 1, 1] := rfl
  calc
    nodeClosure 41 = Subgroup.closure ({word 371, word 355, word 15, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 41)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 42 := rfl

private theorem nodeClosure_eq_42 : nodeClosure 42 = smallEvenDescentNode 43 := by
  have hi : nodeGeneratorIndex 42 = ![371, 355, 254, 124, 113, 3, 5, 1, 1, 1] := rfl
  calc
    nodeClosure 42 = Subgroup.closure ({word 371, word 355, word 254, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 42)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 43 := rfl

private theorem nodeClosure_eq_43 : nodeClosure 43 = smallEvenDescentNode 44 := by
  have hi : nodeGeneratorIndex 43 = ![371, 358, 250, 124, 113, 3, 5, 1, 1, 1] := rfl
  calc
    nodeClosure 43 = Subgroup.closure ({word 371, word 358, word 250, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 43)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 44 := rfl

private theorem nodeClosure_eq_44 : nodeClosure 44 = smallEvenDescentNode 45 := by
  have hi : nodeGeneratorIndex 44 = ![371, 194, 15, 124, 113, 3, 5, 1, 1, 1] := rfl
  calc
    nodeClosure 44 = Subgroup.closure ({word 371, word 194, word 15, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 44)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 45 := rfl

private theorem nodeClosure_eq_45 : nodeClosure 45 = smallEvenDescentNode 46 := by
  have hi : nodeGeneratorIndex 45 = ![371, 358, 254, 124, 113, 3, 5, 1, 1, 1] := rfl
  calc
    nodeClosure 45 = Subgroup.closure ({word 371, word 358, word 254, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 45)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 46 := rfl

private theorem nodeClosure_eq_46 : nodeClosure 46 = smallEvenDescentNode 47 := by
  have hi : nodeGeneratorIndex 46 = ![355, 250, 15, 124, 113, 3, 5, 1, 1, 1] := rfl
  calc
    nodeClosure 46 = Subgroup.closure ({word 355, word 250, word 15, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 46)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 3, rootOne ^ 2, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 47 := rfl

private theorem nodeClosure_eq_47 : nodeClosure 47 = smallEvenDescentNode 48 := by
  have hi : nodeGeneratorIndex 47 = ![157, 355, 15, 124, 113, 3, 5, 1, 1, 1] := rfl
  calc
    nodeClosure 47 = Subgroup.closure ({word 157, word 355, word 15, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 47)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, rootOne ^ 2 * root 0 * root 3, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 48 := rfl

private theorem nodeClosure_eq_48 : nodeClosure 48 = smallEvenDescentNode 49 := by
  have hi : nodeGeneratorIndex 48 = ![44, 250, 15, 124, 113, 3, 5, 1, 1, 1] := rfl
  calc
    nodeClosure 48 = Subgroup.closure ({word 44, word 250, word 15, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 48)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 49 := rfl

private theorem nodeClosure_eq_49 : nodeClosure 49 = smallEvenDescentNode 50 := by
  have hi : nodeGeneratorIndex 49 = ![157, 194, 15, 124, 113, 3, 5, 1, 1, 1] := rfl
  calc
    nodeClosure 49 = Subgroup.closure ({word 157, word 194, word 15, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 49)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 50 := rfl

private theorem nodeClosure_eq_50 : nodeClosure 50 = smallEvenDescentNode 51 := by
  have hi : nodeGeneratorIndex 50 = ![371, 359, 124, 113, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 50 = Subgroup.closure ({word 371, word 359, word 124, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 50)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3 * root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 51 := rfl

private theorem nodeClosure_eq_51 : nodeClosure 51 = smallEvenDescentNode 52 := by
  have hi : nodeGeneratorIndex 51 = ![355, 34, 124, 113, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 51 = Subgroup.closure ({word 355, word 34, word 124, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 51)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 3, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 52 := rfl

private theorem nodeClosure_eq_52 : nodeClosure 52 = smallEvenDescentNode 53 := by
  have hi : nodeGeneratorIndex 52 = ![44, 34, 124, 113, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 52 = Subgroup.closure ({word 44, word 34, word 124, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 52)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 53 := rfl

private theorem nodeClosure_eq_53 : nodeClosure 53 = smallEvenDescentNode 54 := by
  have hi : nodeGeneratorIndex 53 = ![371, 182, 124, 113, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 53 = Subgroup.closure ({word 371, word 182, word 124, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 53)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 0 * root 2 * root 5 * root 6 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 54 := rfl

private theorem nodeClosure_eq_54 : nodeClosure 54 = smallEvenDescentNode 55 := by
  have hi : nodeGeneratorIndex 54 = ![355, 261, 124, 113, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 54 = Subgroup.closure ({word 355, word 261, word 124, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 54)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 3, rootOne ^ 2 * root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 55 := rfl

private theorem nodeClosure_eq_55 : nodeClosure 55 = smallEvenDescentNode 56 := by
  have hi : nodeGeneratorIndex 55 = ![167, 355, 124, 113, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 55 = Subgroup.closure ({word 167, word 355, word 124, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 55)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 56 := rfl

private theorem nodeClosure_eq_56 : nodeClosure 56 = smallEvenDescentNode 57 := by
  have hi : nodeGeneratorIndex 56 = ![167, 182, 124, 113, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 56 = Subgroup.closure ({word 167, word 182, word 124, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 56)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 5 * root 6 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 57 := rfl

private theorem nodeClosure_eq_57 : nodeClosure 57 = smallEvenDescentNode 58 := by
  have hi : nodeGeneratorIndex 57 = ![371, 359, 250, 124, 119, 6, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 57 = Subgroup.closure ({word 371, word 359, word 250, word 124, word 119, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 57)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3 * root 4 * root 7 * root 8, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 58 := rfl

private theorem nodeClosure_eq_58 : nodeClosure 58 = smallEvenDescentNode 59 := by
  have hi : nodeGeneratorIndex 58 = ![371, 359, 254, 124, 119, 6, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 58 = Subgroup.closure ({word 371, word 359, word 254, word 124, word 119, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 58)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 59 := rfl

private theorem nodeClosure_eq_59 : nodeClosure 59 = smallEvenDescentNode 60 := by
  have hi : nodeGeneratorIndex 59 = ![371, 360, 250, 124, 119, 6, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 59 = Subgroup.closure ({word 371, word 360, word 250, word 124, word 119, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 59)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3 * root 4 * root 6 * root 9, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 60 := rfl

private theorem nodeClosure_eq_60 : nodeClosure 60 = smallEvenDescentNode 61 := by
  have hi : nodeGeneratorIndex 60 = ![371, 360, 254, 124, 119, 6, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 60 = Subgroup.closure ({word 371, word 360, word 254, word 124, word 119, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 60)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3 * root 4 * root 6 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 61 := rfl

private theorem nodeClosure_eq_61 : nodeClosure 61 = smallEvenDescentNode 62 := by
  have hi : nodeGeneratorIndex 61 = ![59, 250, 15, 124, 119, 6, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 61 = Subgroup.closure ({word 59, word 250, word 15, word 124, word 119, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 61)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, rootOne ^ 2, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 62 := rfl

private theorem nodeClosure_eq_62 : nodeClosure 62 = smallEvenDescentNode 63 := by
  have hi : nodeGeneratorIndex 62 = ![157, 182, 15, 124, 119, 6, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 62 = Subgroup.closure ({word 157, word 182, word 15, word 124, word 119, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 62)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 2 * root 5 * root 6 * root 9, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 63 := rfl

private theorem nodeClosure_eq_63 : nodeClosure 63 = smallEvenDescentNode 64 := by
  have hi : nodeGeneratorIndex 63 = ![194, 34, 124, 113, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 63 = Subgroup.closure ({word 194, word 34, word 124, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 63)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 64 := rfl

private theorem nodeClosure_eq_64 : nodeClosure 64 = smallEvenDescentNode 65 := by
  have hi : nodeGeneratorIndex 64 = ![266, 34, 124, 113, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 64 = Subgroup.closure ({word 266, word 34, word 124, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 64)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 65 := rfl

private theorem nodeClosure_eq_65 : nodeClosure 65 = smallEvenDescentNode 66 := by
  have hi : nodeGeneratorIndex 65 = ![167, 194, 124, 113, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 65 = Subgroup.closure ({word 167, word 194, word 124, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 65)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 66 := rfl

private theorem nodeClosure_eq_66 : nodeClosure 66 = smallEvenDescentNode 67 := by
  have hi : nodeGeneratorIndex 66 = ![157, 355, 34, 113, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 66 = Subgroup.closure ({word 157, word 355, word 34, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 66)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, rootOne ^ 2 * root 0 * root 3, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 67 := rfl

private theorem nodeClosure_eq_67 : nodeClosure 67 = smallEvenDescentNode 68 := by
  have hi : nodeGeneratorIndex 67 = ![157, 355, 110, 113, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 67 = Subgroup.closure ({word 157, word 355, word 110, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 67)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 5 * root 6 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 68 := rfl

private theorem nodeClosure_eq_68 : nodeClosure 68 = smallEvenDescentNode 69 := by
  have hi : nodeGeneratorIndex 68 = ![157, 367, 34, 113, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 68 = Subgroup.closure ({word 157, word 367, word 34, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 68)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, rootOne ^ 2 * root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 69 := rfl

private theorem nodeClosure_eq_69 : nodeClosure 69 = smallEvenDescentNode 70 := by
  have hi : nodeGeneratorIndex 69 = ![44, 250, 34, 124, 113, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 69 = Subgroup.closure ({word 44, word 250, word 34, word 124, word 113, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 69)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 70 := rfl

private theorem nodeClosure_eq_70 : nodeClosure 70 = smallEvenDescentNode 71 := by
  have hi : nodeGeneratorIndex 70 = ![44, 250, 34, 124, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 70 = Subgroup.closure ({word 44, word 250, word 34, word 124, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 70)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 71 := rfl

private theorem nodeClosure_eq_71 : nodeClosure 71 = smallEvenDescentNode 72 := by
  have hi : nodeGeneratorIndex 71 = ![44, 250, 34, 113, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 71 = Subgroup.closure ({word 44, word 250, word 34, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 71)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 72 := rfl

private theorem nodeClosure_eq_72 : nodeClosure 72 = smallEvenDescentNode 73 := by
  have hi : nodeGeneratorIndex 72 = ![44, 250, 34, 24, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 72 = Subgroup.closure ({word 44, word 250, word 34, word 24, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 72)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 73 := rfl

private theorem nodeClosure_eq_73 : nodeClosure 73 = smallEvenDescentNode 74 := by
  have hi : nodeGeneratorIndex 73 = ![44, 250, 105, 124, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 73 = Subgroup.closure ({word 44, word 250, word 105, word 124, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 73)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 74 := rfl

private theorem nodeClosure_eq_74 : nodeClosure 74 = smallEvenDescentNode 75 := by
  have hi : nodeGeneratorIndex 74 = ![44, 250, 36, 124, 119, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 74 = Subgroup.closure ({word 44, word 250, word 36, word 124, word 119, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 74)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 4 * root 6 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 75 := rfl

private theorem nodeClosure_eq_75 : nodeClosure 75 = smallEvenDescentNode 76 := by
  have hi : nodeGeneratorIndex 75 = ![44, 250, 36, 121, 113, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 75 = Subgroup.closure ({word 44, word 250, word 36, word 121, word 113, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 75)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 4 * root 6 * root 9, root 2 * root 3 * root 4 * root 5 * root 8, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 76 := rfl

private theorem nodeClosure_eq_76 : nodeClosure 76 = smallEvenDescentNode 77 := by
  have hi : nodeGeneratorIndex 76 = ![44, 250, 36, 121, 119, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 76 = Subgroup.closure ({word 44, word 250, word 36, word 121, word 119, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 76)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 4 * root 6 * root 9, root 2 * root 3 * root 4 * root 5 * root 8, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 77 := rfl

private theorem nodeClosure_eq_77 : nodeClosure 77 = smallEvenDescentNode 78 := by
  have hi : nodeGeneratorIndex 77 = ![44, 328, 34, 124, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 77 = Subgroup.closure ({word 44, word 328, word 34, word 124, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 77)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 78 := rfl

private theorem nodeClosure_eq_78 : nodeClosure 78 = smallEvenDescentNode 79 := by
  have hi : nodeGeneratorIndex 78 = ![44, 338, 34, 113, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 78 = Subgroup.closure ({word 44, word 338, word 34, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 78)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 79 := rfl

private theorem nodeClosure_eq_79 : nodeClosure 79 = smallEvenDescentNode 80 := by
  have hi : nodeGeneratorIndex 79 = ![92, 250, 34, 24, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 79 = Subgroup.closure ({word 92, word 250, word 34, word 24, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 79)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 80 := rfl

private theorem nodeClosure_eq_80 : nodeClosure 80 = smallEvenDescentNode 81 := by
  have hi : nodeGeneratorIndex 80 = ![157, 194, 34, 27, 13, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 80 = Subgroup.closure ({word 157, word 194, word 34, word 27, word 13, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 80)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 4 * root 7 * root 8, root 5 * root 6 * root 7, root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 81 := rfl

private theorem nodeClosure_eq_81 : nodeClosure 81 = smallEvenDescentNode 82 := by
  have hi : nodeGeneratorIndex 81 = ![157, 194, 105, 27, 13, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 81 = Subgroup.closure ({word 157, word 194, word 105, word 27, word 13, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 81)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 2 * root 3 * root 7 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 82 := rfl

private theorem nodeClosure_eq_82 : nodeClosure 82 = smallEvenDescentNode 83 := by
  have hi : nodeGeneratorIndex 82 = ![157, 171, 34, 27, 13, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 82 = Subgroup.closure ({word 157, word 171, word 34, word 27, word 13, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 82)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 3 * root 5 * root 6 * root 7, root 4 * root 7 * root 8, root 5 * root 6 * root 7, root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 83 := rfl

private theorem nodeClosure_eq_83 : nodeClosure 83 = smallEvenDescentNode 84 := by
  have hi : nodeGeneratorIndex 83 = ![157, 171, 105, 27, 13, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 83 = Subgroup.closure ({word 157, word 171, word 105, word 27, word 13, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 83)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 3 * root 5 * root 6 * root 7, root 2 * root 3 * root 7 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 84 := rfl

private theorem nodeClosure_eq_84 : nodeClosure 84 = smallEvenDescentNode 85 := by
  have hi : nodeGeneratorIndex 84 = ![131, 124, 116, 34, 8, 6, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 84 = Subgroup.closure ({word 131, word 124, word 116, word 34, word 8, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 84)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 1 * root 5 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 85 := rfl

private theorem nodeClosure_eq_85 : nodeClosure 85 = smallEvenDescentNode 86 := by
  have hi : nodeGeneratorIndex 85 = ![44, 141, 116, 18, 10, 4, 2, 1, 1, 1] := rfl
  calc
    nodeClosure 85 = Subgroup.closure ({word 44, word 141, word 116, word 18, word 10, word 4, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 85)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 5 * root 8, root 6 * root 8, root 7, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 86 := rfl

private theorem nodeClosure_eq_86 : nodeClosure 86 = smallEvenDescentNode 87 := by
  have hi : nodeGeneratorIndex 86 = ![44, 141, 34, 18, 10, 4, 2, 1, 1, 1] := rfl
  calc
    nodeClosure 86 = Subgroup.closure ({word 44, word 141, word 34, word 18, word 10, word 4, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 86)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 5 * root 8, root 6 * root 8, root 7, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 87 := rfl

private theorem nodeClosure_eq_87 : nodeClosure 87 = smallEvenDescentNode 88 := by
  have hi : nodeGeneratorIndex 87 = ![44, 141, 103, 18, 10, 4, 2, 1, 1, 1] := rfl
  calc
    nodeClosure 87 = Subgroup.closure ({word 44, word 141, word 103, word 18, word 10, word 4, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 87)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 8, root 5 * root 8, root 6 * root 8, root 7, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 88 := rfl

private theorem nodeClosure_eq_88 : nodeClosure 88 = smallEvenDescentNode 89 := by
  have hi : nodeGeneratorIndex 88 = ![90, 141, 34, 18, 10, 4, 2, 1, 1, 1] := rfl
  calc
    nodeClosure 88 = Subgroup.closure ({word 90, word 141, word 34, word 18, word 10, word 4, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 88)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 5 * root 8, root 6 * root 8, root 7, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 89 := rfl

private theorem nodeClosure_eq_89 : nodeClosure 89 = smallEvenDescentNode 90 := by
  have hi : nodeGeneratorIndex 89 = ![340, 124, 116, 34, 8, 6, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 89 = Subgroup.closure ({word 340, word 124, word 116, word 34, word 8, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 89)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 1 * root 5 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 90 := rfl

private theorem nodeClosure_eq_90 : nodeClosure 90 = smallEvenDescentNode 91 := by
  have hi : nodeGeneratorIndex 90 = ![220, 355, 111, 114, 9, 5, 2, 1, 1, 1] := rfl
  calc
    nodeClosure 90 = Subgroup.closure ({word 220, word 355, word 111, word 114, word 9, word 5, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 90)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 5 * root 6 * root 8 * root 9, root 2 * root 3 * root 4 * root 8, root 6 * root 9, root 7 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 91 := rfl

private theorem nodeClosure_eq_91 : nodeClosure 91 = smallEvenDescentNode 92 := by
  have hi : nodeGeneratorIndex 91 = ![44, 348, 116, 40, 10, 4, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 91 = Subgroup.closure ({word 44, word 348, word 116, word 40, word 10, word 4, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 91)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 5 * root 8 * root 9, root 6 * root 8, root 7, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 92 := rfl

private theorem nodeClosure_eq_92 : nodeClosure 92 = smallEvenDescentNode 93 := by
  have hi : nodeGeneratorIndex 92 = ![44, 348, 34, 40, 10, 4, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 92 = Subgroup.closure ({word 44, word 348, word 34, word 40, word 10, word 4, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 92)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 4 * root 5 * root 8 * root 9, root 6 * root 8, root 7, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 93 := rfl

private theorem nodeClosure_eq_93 : nodeClosure 93 = smallEvenDescentNode 94 := by
  have hi : nodeGeneratorIndex 93 = ![90, 348, 34, 40, 10, 4, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 93 = Subgroup.closure ({word 90, word 348, word 34, word 40, word 10, word 4, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 93)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 4 * root 5 * root 8 * root 9, root 6 * root 8, root 7, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 94 := rfl

private theorem nodeClosure_eq_94 : nodeClosure 94 = smallEvenDescentNode 95 := by
  have hi : nodeGeneratorIndex 94 = ![131, 250, 17, 35, 15, 7, 2, 1, 1, 1] := rfl
  calc
    nodeClosure 94 = Subgroup.closure ({word 131, word 250, word 17, word 35, word 15, word 7, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 94)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 1 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 5 * root 9, root 4 * root 7 * root 8 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 8 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 95 := rfl

private theorem nodeClosure_eq_95 : nodeClosure 95 = smallEvenDescentNode 96 := by
  have hi : nodeGeneratorIndex 95 = ![157, 235, 116, 22, 8, 5, 2, 1, 1, 1] := rfl
  calc
    nodeClosure 95 = Subgroup.closure ({word 157, word 235, word 116, word 22, word 8, word 5, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 95)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 2 * root 3 * root 4 * root 7, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 96 := rfl

private theorem nodeClosure_eq_96 : nodeClosure 96 = smallEvenDescentNode 97 := by
  have hi : nodeGeneratorIndex 96 = ![157, 235, 34, 22, 8, 5, 2, 1, 1, 1] := rfl
  calc
    nodeClosure 96 = Subgroup.closure ({word 157, word 235, word 34, word 22, word 8, word 5, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 96)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 4 * root 7 * root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 97 := rfl

private theorem nodeClosure_eq_97 : nodeClosure 97 = smallEvenDescentNode 98 := by
  have hi : nodeGeneratorIndex 97 = ![157, 235, 103, 22, 8, 5, 2, 1, 1, 1] := rfl
  calc
    nodeClosure 97 = Subgroup.closure ({word 157, word 235, word 103, word 22, word 8, word 5, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 97)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 2 * root 3 * root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 98 := rfl

private theorem nodeClosure_eq_98 : nodeClosure 98 = smallEvenDescentNode 99 := by
  have hi : nodeGeneratorIndex 98 = ![157, 213, 34, 22, 8, 5, 2, 1, 1, 1] := rfl
  calc
    nodeClosure 98 = Subgroup.closure ({word 157, word 213, word 34, word 22, word 8, word 5, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 98)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 1 * root 4 * root 6, root 4 * root 7 * root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 99 := rfl

private theorem nodeClosure_eq_99 : nodeClosure 99 = smallEvenDescentNode 100 := by
  have hi : nodeGeneratorIndex 99 = ![157, 246, 103, 22, 8, 5, 2, 1, 1, 1] := rfl
  calc
    nodeClosure 99 = Subgroup.closure ({word 157, word 246, word 103, word 22, word 8, word 5, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 99)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 7, root 2 * root 3 * root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 100 := rfl

private theorem nodeClosure_eq_100 : nodeClosure 100 = smallEvenDescentNode 101 := by
  have hi : nodeGeneratorIndex 100 = ![167, 235, 116, 22, 8, 5, 2, 1, 1, 1] := rfl
  calc
    nodeClosure 100 = Subgroup.closure ({word 167, word 235, word 116, word 22, word 8, word 5, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 100)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 2 * root 3 * root 4 * root 7, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 101 := rfl

private theorem nodeClosure_eq_101 : nodeClosure 101 = smallEvenDescentNode 102 := by
  have hi : nodeGeneratorIndex 101 = ![194, 141, 116, 30, 12, 6, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 101 = Subgroup.closure ({word 194, word 141, word 116, word 30, word 12, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 101)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 102 := rfl

private theorem nodeClosure_eq_102 : nodeClosure 102 = smallEvenDescentNode 103 := by
  have hi : nodeGeneratorIndex 102 = ![194, 141, 34, 30, 12, 6, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 102 = Subgroup.closure ({word 194, word 141, word 34, word 30, word 12, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 102)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 103 := rfl

private theorem nodeClosure_eq_103 : nodeClosure 103 = smallEvenDescentNode 104 := by
  have hi : nodeGeneratorIndex 103 = ![194, 141, 103, 30, 12, 6, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 103 = Subgroup.closure ({word 194, word 141, word 103, word 30, word 12, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 103)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 8, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 104 := rfl

private theorem nodeClosure_eq_104 : nodeClosure 104 = smallEvenDescentNode 105 := by
  have hi : nodeGeneratorIndex 104 = ![266, 141, 18, 34, 10, 7, 2, 1, 1, 1] := rfl
  calc
    nodeClosure 104 = Subgroup.closure ({word 266, word 141, word 18, word 34, word 10, word 7, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 104)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8, root 4 * root 7 * root 8, root 6 * root 8, root 7 * root 8 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 105 := rfl

private theorem nodeClosure_eq_105 : nodeClosure 105 = smallEvenDescentNode 106 := by
  have hi : nodeGeneratorIndex 105 = ![131, 348, 17, 32, 15, 6, 2, 1, 1, 1] := rfl
  calc
    nodeClosure 105 = Subgroup.closure ({word 131, word 348, word 17, word 32, word 15, word 6, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 105)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 1 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 9, root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 8, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 106 := rfl

private theorem nodeClosure_eq_106 : nodeClosure 106 = smallEvenDescentNode 107 := by
  have hi : nodeGeneratorIndex 106 = ![44, 250, 141, 18, 35, 2, 7, 1, 1, 1] := rfl
  calc
    nodeClosure 106 = Subgroup.closure ({word 44, word 250, word 141, word 18, word 35, word 2, word 7, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 106)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8, root 4 * root 7 * root 8 * root 9, root 8, root 7 * root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 107 := rfl

private theorem nodeClosure_eq_107 : nodeClosure 107 = smallEvenDescentNode 108 := by
  have hi : nodeGeneratorIndex 107 = ![44, 252, 141, 18, 35, 2, 7, 1, 1, 1] := rfl
  calc
    nodeClosure 107 = Subgroup.closure ({word 44, word 252, word 141, word 18, word 35, word 2, word 7, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 107)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 6 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8, root 4 * root 7 * root 8 * root 9, root 8, root 7 * root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 108 := rfl

private theorem nodeClosure_eq_108 : nodeClosure 108 = smallEvenDescentNode 109 := by
  have hi : nodeGeneratorIndex 108 = ![46, 250, 141, 18, 35, 2, 7, 1, 1, 1] := rfl
  calc
    nodeClosure 108 = Subgroup.closure ({word 46, word 250, word 141, word 18, word 35, word 2, word 7, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 108)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 8, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8, root 4 * root 7 * root 8 * root 9, root 8, root 7 * root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 109 := rfl

private theorem nodeClosure_eq_109 : nodeClosure 109 = smallEvenDescentNode 110 := by
  have hi : nodeGeneratorIndex 109 = ![46, 252, 141, 18, 35, 2, 7, 1, 1, 1] := rfl
  calc
    nodeClosure 109 = Subgroup.closure ({word 46, word 252, word 141, word 18, word 35, word 2, word 7, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 109)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 8, rootOne ^ 2 * root 6 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8, root 4 * root 7 * root 8 * root 9, root 8, root 7 * root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 110 := rfl

private theorem nodeClosure_eq_110 : nodeClosure 110 = smallEvenDescentNode 111 := by
  have hi : nodeGeneratorIndex 110 = ![157, 194, 141, 27, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 110 = Subgroup.closure ({word 157, word 194, word 141, word 27, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 110)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 111 := rfl

private theorem nodeClosure_eq_111 : nodeClosure 111 = smallEvenDescentNode 112 := by
  have hi : nodeGeneratorIndex 111 = ![157, 194, 148, 27, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 111 = Subgroup.closure ({word 157, word 194, word 148, word 27, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 111)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 112 := rfl

private theorem nodeClosure_eq_112 : nodeClosure 112 = smallEvenDescentNode 113 := by
  have hi : nodeGeneratorIndex 112 = ![157, 169, 141, 27, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 112 = Subgroup.closure ({word 157, word 169, word 141, word 27, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 112)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 3 * root 5 * root 6 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 113 := rfl

private theorem nodeClosure_eq_113 : nodeClosure 113 = smallEvenDescentNode 114 := by
  have hi : nodeGeneratorIndex 113 = ![157, 169, 148, 27, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 113 = Subgroup.closure ({word 157, word 169, word 148, word 27, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 113)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 3 * root 5 * root 6 * root 9, root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 114 := rfl

private theorem nodeClosure_eq_114 : nodeClosure 114 = smallEvenDescentNode 115 := by
  have hi : nodeGeneratorIndex 114 = ![200, 194, 141, 27, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 114 = Subgroup.closure ({word 200, word 194, word 141, word 27, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 114)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 115 := rfl

private theorem nodeClosure_eq_115 : nodeClosure 115 = smallEvenDescentNode 116 := by
  have hi : nodeGeneratorIndex 115 = ![200, 194, 148, 27, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 115 = Subgroup.closure ({word 200, word 194, word 148, word 27, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 115)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 116 := rfl

private theorem nodeClosure_eq_116 : nodeClosure 116 = smallEvenDescentNode 117 := by
  have hi : nodeGeneratorIndex 116 = ![200, 169, 148, 27, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 116 = Subgroup.closure ({word 200, word 169, word 148, word 27, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 116)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 3 * root 5 * root 6 * root 9, root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 117 := rfl

private theorem nodeClosure_eq_117 : nodeClosure 117 = smallEvenDescentNode 118 := by
  have hi : nodeGeneratorIndex 117 = ![157, 182, 141, 27, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 117 = Subgroup.closure ({word 157, word 182, word 141, word 27, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 117)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 2 * root 5 * root 6 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 118 := rfl

private theorem nodeClosure_eq_118 : nodeClosure 118 = smallEvenDescentNode 119 := by
  have hi : nodeGeneratorIndex 118 = ![157, 182, 144, 27, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 118 = Subgroup.closure ({word 157, word 182, word 144, word 27, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 118)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 2 * root 5 * root 6 * root 9, root 1 * root 3 * root 4 * root 5 * root 6 * root 8, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 119 := rfl

private theorem nodeClosure_eq_119 : nodeClosure 119 = smallEvenDescentNode 120 := by
  have hi : nodeGeneratorIndex 119 = ![167, 194, 141, 27, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 119 = Subgroup.closure ({word 167, word 194, word 141, word 27, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 119)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 120 := rfl

private theorem nodeClosure_eq_120 : nodeClosure 120 = smallEvenDescentNode 121 := by
  have hi : nodeGeneratorIndex 120 = ![167, 194, 144, 27, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 120 = Subgroup.closure ({word 167, word 194, word 144, word 27, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 120)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 4 * root 5 * root 6 * root 8, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 121 := rfl

private theorem nodeClosure_eq_121 : nodeClosure 121 = smallEvenDescentNode 122 := by
  have hi : nodeGeneratorIndex 121 = ![167, 182, 144, 27, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 121 = Subgroup.closure ({word 167, word 182, word 144, word 27, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 121)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 5 * root 6 * root 9, root 1 * root 3 * root 4 * root 5 * root 6 * root 8, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 122 := rfl

private theorem nodeClosure_eq_122 : nodeClosure 122 = smallEvenDescentNode 123 := by
  have hi : nodeGeneratorIndex 122 = ![157, 177, 141, 27, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 122 = Subgroup.closure ({word 157, word 177, word 141, word 27, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 122)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 3 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 123 := rfl

private theorem nodeClosure_eq_123 : nodeClosure 123 = smallEvenDescentNode 124 := by
  have hi : nodeGeneratorIndex 123 = ![157, 177, 146, 27, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 123 = Subgroup.closure ({word 157, word 177, word 146, word 27, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 123)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 3 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 2 * root 5 * root 6, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 124 := rfl

private theorem nodeClosure_eq_124 : nodeClosure 124 = smallEvenDescentNode 125 := by
  have hi : nodeGeneratorIndex 124 = ![196, 194, 141, 27, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 124 = Subgroup.closure ({word 196, word 194, word 141, word 27, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 124)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 3 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 125 := rfl

private theorem nodeClosure_eq_125 : nodeClosure 125 = smallEvenDescentNode 126 := by
  have hi : nodeGeneratorIndex 125 = ![196, 194, 146, 27, 15, 5, 3, 1, 1, 1] := rfl
  calc
    nodeClosure 125 = Subgroup.closure ({word 196, word 194, word 146, word 27, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 125)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 3 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 2 * root 5 * root 6, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 126 := rfl

private theorem nodeClosure_eq_126 : nodeClosure 126 = smallEvenDescentNode 127 := by
  have hi : nodeGeneratorIndex 126 = ![371, 355, 124, 113, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 126 = Subgroup.closure ({word 371, word 355, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 126)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 127 := rfl

private theorem nodeClosure_eq_127 : nodeClosure 127 = smallEvenDescentNode 128 := by
  have hi : nodeGeneratorIndex 127 = ![371, 194, 124, 113, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 127 = Subgroup.closure ({word 371, word 194, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 127)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 128 := rfl

private theorem nodeClosure_eq_128 : nodeClosure 128 = smallEvenDescentNode 129 := by
  have hi : nodeGeneratorIndex 128 = ![355, 250, 124, 113, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 128 = Subgroup.closure ({word 355, word 250, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 128)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 3, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 129 := rfl

private theorem nodeClosure_eq_129 : nodeClosure 129 = smallEvenDescentNode 130 := by
  have hi : nodeGeneratorIndex 129 = ![157, 355, 124, 113, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 129 = Subgroup.closure ({word 157, word 355, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 129)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 130 := rfl

private theorem nodeClosure_eq_130 : nodeClosure 130 = smallEvenDescentNode 131 := by
  have hi : nodeGeneratorIndex 130 = ![44, 250, 124, 113, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 130 = Subgroup.closure ({word 44, word 250, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 130)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 131 := rfl

private theorem nodeClosure_eq_131 : nodeClosure 131 = smallEvenDescentNode 132 := by
  have hi : nodeGeneratorIndex 131 = ![157, 194, 124, 113, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 131 = Subgroup.closure ({word 157, word 194, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 131)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 132 := rfl

private theorem nodeClosure_eq_132 : nodeClosure 132 = smallEvenDescentNode 133 := by
  have hi : nodeGeneratorIndex 132 = ![371, 358, 124, 113, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 132 = Subgroup.closure ({word 371, word 358, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 132)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 133 := rfl

private theorem nodeClosure_eq_133 : nodeClosure 133 = smallEvenDescentNode 134 := by
  have hi : nodeGeneratorIndex 133 = ![355, 15, 124, 113, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 133 = Subgroup.closure ({word 355, word 15, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 133)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 3, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 134 := rfl

private theorem nodeClosure_eq_134 : nodeClosure 134 = smallEvenDescentNode 135 := by
  have hi : nodeGeneratorIndex 134 = ![44, 15, 124, 113, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 134 = Subgroup.closure ({word 44, word 15, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 134)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 135 := rfl

private theorem nodeClosure_eq_135 : nodeClosure 135 = smallEvenDescentNode 136 := by
  have hi : nodeGeneratorIndex 135 = ![371, 187, 124, 113, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 135 = Subgroup.closure ({word 371, word 187, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 135)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 0 * root 2 * root 4 * root 5 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 136 := rfl

private theorem nodeClosure_eq_136 : nodeClosure 136 = smallEvenDescentNode 137 := by
  have hi : nodeGeneratorIndex 136 = ![355, 254, 124, 113, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 136 = Subgroup.closure ({word 355, word 254, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 136)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 137 := rfl

private theorem nodeClosure_eq_137 : nodeClosure 137 = smallEvenDescentNode 138 := by
  have hi : nodeGeneratorIndex 137 = ![161, 355, 124, 113, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 137 = Subgroup.closure ({word 161, word 355, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 137)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 138 := rfl

private theorem nodeClosure_eq_138 : nodeClosure 138 = smallEvenDescentNode 139 := by
  have hi : nodeGeneratorIndex 138 = ![44, 254, 124, 113, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 138 = Subgroup.closure ({word 44, word 254, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 138)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 139 := rfl

private theorem nodeClosure_eq_139 : nodeClosure 139 = smallEvenDescentNode 140 := by
  have hi : nodeGeneratorIndex 139 = ![49, 250, 124, 113, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 139 = Subgroup.closure ({word 49, word 250, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 139)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 140 := rfl

private theorem nodeClosure_eq_140 : nodeClosure 140 = smallEvenDescentNode 141 := by
  have hi : nodeGeneratorIndex 140 = ![157, 189, 124, 113, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 140 = Subgroup.closure ({word 157, word 189, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 140)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 2 * root 4 * root 5 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 141 := rfl

private theorem nodeClosure_eq_141 : nodeClosure 141 = smallEvenDescentNode 142 := by
  have hi : nodeGeneratorIndex 141 = ![194, 15, 124, 113, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 141 = Subgroup.closure ({word 194, word 15, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 141)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 142 := rfl

private theorem nodeClosure_eq_142 : nodeClosure 142 = smallEvenDescentNode 143 := by
  have hi : nodeGeneratorIndex 142 = ![266, 15, 124, 113, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 142 = Subgroup.closure ({word 266, word 15, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 142)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 143 := rfl

private theorem nodeClosure_eq_143 : nodeClosure 143 = smallEvenDescentNode 144 := by
  have hi : nodeGeneratorIndex 143 = ![49, 254, 124, 113, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 143 = Subgroup.closure ({word 49, word 254, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 143)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 144 := rfl

private theorem nodeClosure_eq_144 : nodeClosure 144 = smallEvenDescentNode 145 := by
  have hi : nodeGeneratorIndex 144 = ![157, 355, 15, 113, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 144 = Subgroup.closure ({word 157, word 355, word 15, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 144)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, rootOne ^ 2 * root 0 * root 3, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 145 := rfl

private theorem nodeClosure_eq_145 : nodeClosure 145 = smallEvenDescentNode 146 := by
  have hi : nodeGeneratorIndex 145 = ![157, 355, 122, 113, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 145 = Subgroup.closure ({word 157, word 355, word 122, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 145)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 146 := rfl

private theorem nodeClosure_eq_146 : nodeClosure 146 = smallEvenDescentNode 147 := by
  have hi : nodeGeneratorIndex 146 = ![157, 367, 15, 113, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 146 = Subgroup.closure ({word 157, word 367, word 15, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 146)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, rootOne ^ 2 * root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 147 := rfl

private theorem nodeClosure_eq_147 : nodeClosure 147 = smallEvenDescentNode 148 := by
  have hi : nodeGeneratorIndex 147 = ![157, 367, 122, 113, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 147 = Subgroup.closure ({word 157, word 367, word 122, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 147)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, rootOne ^ 2 * root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 148 := rfl

private theorem nodeClosure_eq_148 : nodeClosure 148 = smallEvenDescentNode 149 := by
  have hi : nodeGeneratorIndex 148 = ![44, 250, 15, 124, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 148 = Subgroup.closure ({word 44, word 250, word 15, word 124, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 148)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 149 := rfl

private theorem nodeClosure_eq_149 : nodeClosure 149 = smallEvenDescentNode 150 := by
  have hi : nodeGeneratorIndex 149 = ![44, 250, 15, 113, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 149 = Subgroup.closure ({word 44, word 250, word 15, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 149)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 150 := rfl

private theorem nodeClosure_eq_150 : nodeClosure 150 = smallEvenDescentNode 151 := by
  have hi : nodeGeneratorIndex 150 = ![44, 250, 15, 24, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 150 = Subgroup.closure ({word 44, word 250, word 15, word 24, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 150)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 151 := rfl

private theorem nodeClosure_eq_151 : nodeClosure 151 = smallEvenDescentNode 152 := by
  have hi : nodeGeneratorIndex 151 = ![44, 250, 120, 124, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 151 = Subgroup.closure ({word 44, word 250, word 120, word 124, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 151)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 152 := rfl

private theorem nodeClosure_eq_152 : nodeClosure 152 = smallEvenDescentNode 153 := by
  have hi : nodeGeneratorIndex 152 = ![44, 250, 122, 113, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 152 = Subgroup.closure ({word 44, word 250, word 122, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 152)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 153 := rfl

private theorem nodeClosure_eq_153 : nodeClosure 153 = smallEvenDescentNode 154 := by
  have hi : nodeGeneratorIndex 153 = ![44, 250, 120, 24, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 153 = Subgroup.closure ({word 44, word 250, word 120, word 24, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 153)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 154 := rfl

private theorem nodeClosure_eq_154 : nodeClosure 154 = smallEvenDescentNode 155 := by
  have hi : nodeGeneratorIndex 154 = ![44, 328, 15, 124, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 154 = Subgroup.closure ({word 44, word 328, word 15, word 124, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 154)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 155 := rfl

private theorem nodeClosure_eq_155 : nodeClosure 155 = smallEvenDescentNode 156 := by
  have hi : nodeGeneratorIndex 155 = ![44, 338, 15, 113, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 155 = Subgroup.closure ({word 44, word 338, word 15, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 155)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 156 := rfl

private theorem nodeClosure_eq_156 : nodeClosure 156 = smallEvenDescentNode 157 := by
  have hi : nodeGeneratorIndex 156 = ![44, 328, 120, 124, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 156 = Subgroup.closure ({word 44, word 328, word 120, word 124, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 156)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 157 := rfl

private theorem nodeClosure_eq_157 : nodeClosure 157 = smallEvenDescentNode 158 := by
  have hi : nodeGeneratorIndex 157 = ![44, 338, 122, 113, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 157 = Subgroup.closure ({word 44, word 338, word 122, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 157)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 158 := rfl

private theorem nodeClosure_eq_158 : nodeClosure 158 = smallEvenDescentNode 159 := by
  have hi : nodeGeneratorIndex 158 = ![92, 250, 15, 24, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 158 = Subgroup.closure ({word 92, word 250, word 15, word 24, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 158)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2, root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 159 := rfl

private theorem nodeClosure_eq_159 : nodeClosure 159 = smallEvenDescentNode 160 := by
  have hi : nodeGeneratorIndex 159 = ![92, 250, 120, 24, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 159 = Subgroup.closure ({word 92, word 250, word 120, word 24, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 159)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 160 := rfl

private theorem nodeClosure_eq_160 : nodeClosure 160 = smallEvenDescentNode 161 := by
  have hi : nodeGeneratorIndex 160 = ![157, 194, 15, 27, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 160 = Subgroup.closure ({word 157, word 194, word 15, word 27, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 160)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 7, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 161 := rfl

private theorem nodeClosure_eq_161 : nodeClosure 161 = smallEvenDescentNode 162 := by
  have hi : nodeGeneratorIndex 161 = ![157, 171, 15, 27, 3, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 161 = Subgroup.closure ({word 157, word 171, word 15, word 27, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 161)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 3 * root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 7, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 162 := rfl

private theorem nodeClosure_eq_162 : nodeClosure 162 = smallEvenDescentNode 163 := by
  have hi : nodeGeneratorIndex 162 = ![371, 359, 124, 119, 6, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 162 = Subgroup.closure ({word 371, word 359, word 124, word 119, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 162)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3 * root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 163 := rfl

private theorem nodeClosure_eq_163 : nodeClosure 163 = smallEvenDescentNode 164 := by
  have hi : nodeGeneratorIndex 163 = ![371, 360, 124, 119, 6, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 163 = Subgroup.closure ({word 371, word 360, word 124, word 119, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 163)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3 * root 4 * root 6 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 164 := rfl

private theorem nodeClosure_eq_164 : nodeClosure 164 = smallEvenDescentNode 165 := by
  have hi : nodeGeneratorIndex 164 = ![59, 15, 124, 119, 6, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 164 = Subgroup.closure ({word 59, word 15, word 124, word 119, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 164)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 165 := rfl

private theorem nodeClosure_eq_165 : nodeClosure 165 = smallEvenDescentNode 166 := by
  have hi : nodeGeneratorIndex 165 = ![355, 34, 113, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 165 = Subgroup.closure ({word 355, word 34, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 165)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 3, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 166 := rfl

private theorem nodeClosure_eq_166 : nodeClosure 166 = smallEvenDescentNode 167 := by
  have hi : nodeGeneratorIndex 166 = ![355, 110, 113, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 166 = Subgroup.closure ({word 355, word 110, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 166)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 5 * root 6 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 167 := rfl

private theorem nodeClosure_eq_167 : nodeClosure 167 = smallEvenDescentNode 168 := by
  have hi : nodeGeneratorIndex 167 = ![44, 34, 124, 113, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 167 = Subgroup.closure ({word 44, word 34, word 124, word 113, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 167)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 168 := rfl

private theorem nodeClosure_eq_168 : nodeClosure 168 = smallEvenDescentNode 169 := by
  have hi : nodeGeneratorIndex 168 = ![44, 34, 124, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 168 = Subgroup.closure ({word 44, word 34, word 124, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 168)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 169 := rfl

private theorem nodeClosure_eq_169 : nodeClosure 169 = smallEvenDescentNode 170 := by
  have hi : nodeGeneratorIndex 169 = ![44, 34, 113, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 169 = Subgroup.closure ({word 44, word 34, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 169)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 170 := rfl

private theorem nodeClosure_eq_170 : nodeClosure 170 = smallEvenDescentNode 171 := by
  have hi : nodeGeneratorIndex 170 = ![44, 34, 24, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 170 = Subgroup.closure ({word 44, word 34, word 24, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 170)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 171 := rfl

private theorem nodeClosure_eq_171 : nodeClosure 171 = smallEvenDescentNode 172 := by
  have hi : nodeGeneratorIndex 171 = ![44, 105, 124, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 171 = Subgroup.closure ({word 44, word 105, word 124, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 171)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 172 := rfl

private theorem nodeClosure_eq_172 : nodeClosure 172 = smallEvenDescentNode 173 := by
  have hi : nodeGeneratorIndex 172 = ![44, 36, 124, 119, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 172 = Subgroup.closure ({word 44, word 36, word 124, word 119, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 172)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 4 * root 6 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 173 := rfl

private theorem nodeClosure_eq_173 : nodeClosure 173 = smallEvenDescentNode 174 := by
  have hi : nodeGeneratorIndex 173 = ![92, 34, 24, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 173 = Subgroup.closure ({word 92, word 34, word 24, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 173)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 174 := rfl

private theorem nodeClosure_eq_174 : nodeClosure 174 = smallEvenDescentNode 175 := by
  have hi : nodeGeneratorIndex 174 = ![371, 182, 124, 118, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 174 = Subgroup.closure ({word 371, word 182, word 124, word 118, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 174)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 0 * root 2 * root 5 * root 6 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 175 := rfl

private theorem nodeClosure_eq_175 : nodeClosure 175 = smallEvenDescentNode 176 := by
  have hi : nodeGeneratorIndex 175 = ![371, 181, 124, 118, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 175 = Subgroup.closure ({word 371, word 181, word 124, word 118, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 175)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 0 * root 2 * root 5 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 176 := rfl

private theorem nodeClosure_eq_176 : nodeClosure 176 = smallEvenDescentNode 177 := by
  have hi : nodeGeneratorIndex 176 = ![182, 15, 124, 118, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 176 = Subgroup.closure ({word 182, word 15, word 124, word 118, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 176)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 5 * root 6 * root 9, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 177 := rfl

private theorem nodeClosure_eq_177 : nodeClosure 177 = smallEvenDescentNode 178 := by
  have hi : nodeGeneratorIndex 177 = ![355, 261, 121, 114, 6, 2, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 177 = Subgroup.closure ({word 355, word 261, word 121, word 114, word 6, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 177)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 3, rootOne ^ 2 * root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 8, root 2 * root 3 * root 4 * root 8, root 7 * root 8, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 178 := rfl

private theorem nodeClosure_eq_178 : nodeClosure 178 = smallEvenDescentNode 179 := by
  have hi : nodeGeneratorIndex 178 = ![355, 262, 121, 114, 6, 2, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 178 = Subgroup.closure ({word 355, word 262, word 121, word 114, word 6, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 178)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 3, rootOne ^ 2 * root 4 * root 6 * root 9, root 2 * root 3 * root 4 * root 5 * root 8, root 2 * root 3 * root 4 * root 8, root 7 * root 8, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 179 := rfl

private theorem nodeClosure_eq_179 : nodeClosure 179 = smallEvenDescentNode 180 := by
  have hi : nodeGeneratorIndex 179 = ![167, 355, 113, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 179 = Subgroup.closure ({word 167, word 355, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 179)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 180 := rfl

private theorem nodeClosure_eq_180 : nodeClosure 180 = smallEvenDescentNode 181 := by
  have hi : nodeGeneratorIndex 180 = ![167, 367, 113, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 180 = Subgroup.closure ({word 167, word 367, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 180)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, rootOne ^ 2 * root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 181 := rfl

private theorem nodeClosure_eq_181 : nodeClosure 181 = smallEvenDescentNode 182 := by
  have hi : nodeGeneratorIndex 181 = ![167, 182, 30, 13, 7, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 181 = Subgroup.closure ({word 167, word 182, word 30, word 13, word 7, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 181)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 5 * root 6 * root 9, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7 * root 9, root 7 * root 8 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 182 := rfl

private theorem nodeClosure_eq_182 : nodeClosure 182 = smallEvenDescentNode 183 := by
  have hi : nodeGeneratorIndex 182 = ![167, 174, 30, 13, 7, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 182 = Subgroup.closure ({word 167, word 174, word 30, word 13, word 7, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 182)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 3 * root 4 * root 5 * root 6 * root 9, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7 * root 9, root 7 * root 8 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 183 := rfl

private theorem nodeClosure_eq_183 : nodeClosure 183 = smallEvenDescentNode 184 := by
  have hi : nodeGeneratorIndex 183 = ![59, 250, 124, 119, 6, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 183 = Subgroup.closure ({word 59, word 250, word 124, word 119, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 183)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 184 := rfl

private theorem nodeClosure_eq_184 : nodeClosure 184 = smallEvenDescentNode 185 := by
  have hi : nodeGeneratorIndex 184 = ![59, 254, 124, 119, 6, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 184 = Subgroup.closure ({word 59, word 254, word 124, word 119, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 184)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 185 := rfl

private theorem nodeClosure_eq_185 : nodeClosure 185 = smallEvenDescentNode 186 := by
  have hi : nodeGeneratorIndex 185 = ![61, 250, 124, 119, 6, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 185 = Subgroup.closure ({word 61, word 250, word 124, word 119, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 185)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 6 * root 9, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 186 := rfl

private theorem nodeClosure_eq_186 : nodeClosure 186 = smallEvenDescentNode 187 := by
  have hi : nodeGeneratorIndex 186 = ![61, 254, 124, 119, 6, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 186 = Subgroup.closure ({word 61, word 254, word 124, word 119, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 186)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 6 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 187 := rfl

private theorem nodeClosure_eq_187 : nodeClosure 187 = smallEvenDescentNode 188 := by
  have hi : nodeGeneratorIndex 187 = ![59, 250, 15, 124, 6, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 187 = Subgroup.closure ({word 59, word 250, word 15, word 124, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 187)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, rootOne ^ 2, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 188 := rfl

private theorem nodeClosure_eq_188 : nodeClosure 188 = smallEvenDescentNode 189 := by
  have hi : nodeGeneratorIndex 188 = ![59, 250, 15, 119, 6, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 188 = Subgroup.closure ({word 59, word 250, word 15, word 119, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 188)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, rootOne ^ 2, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 189 := rfl

private theorem nodeClosure_eq_189 : nodeClosure 189 = smallEvenDescentNode 190 := by
  have hi : nodeGeneratorIndex 189 = ![59, 250, 112, 124, 6, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 189 = Subgroup.closure ({word 59, word 250, word 112, word 124, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 189)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, rootOne ^ 2, root 2 * root 3 * root 4, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 190 := rfl

private theorem nodeClosure_eq_190 : nodeClosure 190 = smallEvenDescentNode 191 := by
  have hi : nodeGeneratorIndex 190 = ![59, 250, 122, 119, 6, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 190 = Subgroup.closure ({word 59, word 250, word 122, word 119, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 190)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 191 := rfl

private theorem nodeClosure_eq_191 : nodeClosure 191 = smallEvenDescentNode 192 := by
  have hi : nodeGeneratorIndex 191 = ![59, 250, 112, 21, 6, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 191 = Subgroup.closure ({word 59, word 250, word 112, word 21, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 191)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, rootOne ^ 2, root 2 * root 3 * root 4, root 5 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 192 := rfl

private theorem nodeClosure_eq_192 : nodeClosure 192 = smallEvenDescentNode 193 := by
  have hi : nodeGeneratorIndex 192 = ![59, 330, 15, 124, 6, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 192 = Subgroup.closure ({word 59, word 330, word 15, word 124, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 192)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 193 := rfl

private theorem nodeClosure_eq_193 : nodeClosure 193 = smallEvenDescentNode 194 := by
  have hi : nodeGeneratorIndex 193 = ![59, 338, 15, 119, 6, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 193 = Subgroup.closure ({word 59, word 338, word 15, word 119, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 193)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 194 := rfl

private theorem nodeClosure_eq_194 : nodeClosure 194 = smallEvenDescentNode 195 := by
  have hi : nodeGeneratorIndex 194 = ![59, 330, 112, 124, 6, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 194 = Subgroup.closure ({word 59, word 330, word 112, word 124, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 194)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 2 * root 3 * root 4, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 195 := rfl

private theorem nodeClosure_eq_195 : nodeClosure 195 = smallEvenDescentNode 196 := by
  have hi : nodeGeneratorIndex 195 = ![59, 338, 122, 119, 6, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 195 = Subgroup.closure ({word 59, word 338, word 122, word 119, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 195)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 196 := rfl

private theorem nodeClosure_eq_196 : nodeClosure 196 = smallEvenDescentNode 197 := by
  have hi : nodeGeneratorIndex 196 = ![76, 250, 15, 21, 6, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 196 = Subgroup.closure ({word 76, word 250, word 15, word 21, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 196)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 6 * root 7, rootOne ^ 2, root 6 * root 7 * root 8 * root 9, root 5 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 197 := rfl

private theorem nodeClosure_eq_197 : nodeClosure 197 = smallEvenDescentNode 198 := by
  have hi : nodeGeneratorIndex 197 = ![76, 250, 112, 21, 6, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 197 = Subgroup.closure ({word 76, word 250, word 112, word 21, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 197)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 6 * root 7, rootOne ^ 2, root 2 * root 3 * root 4, root 5 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 198 := rfl

private theorem nodeClosure_eq_198 : nodeClosure 198 = smallEvenDescentNode 199 := by
  have hi : nodeGeneratorIndex 198 = ![157, 182, 15, 16, 4, 2, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 198 = Subgroup.closure ({word 157, word 182, word 15, word 16, word 4, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 198)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 2 * root 5 * root 6 * root 9, root 6 * root 7 * root 8 * root 9, root 5, root 7, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 199 := rfl

private theorem nodeClosure_eq_199 : nodeClosure 199 = smallEvenDescentNode 200 := by
  have hi : nodeGeneratorIndex 199 = ![157, 173, 15, 16, 4, 2, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 199 = Subgroup.closure ({word 157, word 173, word 15, word 16, word 4, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 199)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 3 * root 4 * root 5 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 5, root 7, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 200 := rfl

private theorem nodeClosure_eq_200 : nodeClosure 200 = smallEvenDescentNode 201 := by
  have hi : nodeGeneratorIndex 200 = ![194, 34, 30, 14, 5, 2, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 200 = Subgroup.closure ({word 194, word 34, word 30, word 14, word 5, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 200)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 4 * root 7 * root 8, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7 * root 8, root 7 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 201 := rfl

private theorem nodeClosure_eq_201 : nodeClosure 201 = smallEvenDescentNode 202 := by
  have hi : nodeGeneratorIndex 201 = ![194, 105, 30, 14, 5, 2, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 201 = Subgroup.closure ({word 194, word 105, word 30, word 14, word 5, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 201)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 2 * root 3 * root 7 * root 9, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7 * root 8, root 7 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 202 := rfl

private theorem nodeClosure_eq_202 : nodeClosure 202 = smallEvenDescentNode 203 := by
  have hi : nodeGeneratorIndex 202 = ![266, 34, 124, 113, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 202 = Subgroup.closure ({word 266, word 34, word 124, word 113, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 202)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 203 := rfl

private theorem nodeClosure_eq_203 : nodeClosure 203 = smallEvenDescentNode 204 := by
  have hi : nodeGeneratorIndex 203 = ![266, 34, 124, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 203 = Subgroup.closure ({word 266, word 34, word 124, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 203)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 204 := rfl

private theorem nodeClosure_eq_204 : nodeClosure 204 = smallEvenDescentNode 205 := by
  have hi : nodeGeneratorIndex 204 = ![266, 34, 113, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 204 = Subgroup.closure ({word 266, word 34, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 204)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 205 := rfl

private theorem nodeClosure_eq_205 : nodeClosure 205 = smallEvenDescentNode 206 := by
  have hi : nodeGeneratorIndex 205 = ![266, 34, 24, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 205 = Subgroup.closure ({word 266, word 34, word 24, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 205)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 206 := rfl

private theorem nodeClosure_eq_206 : nodeClosure 206 = smallEvenDescentNode 207 := by
  have hi : nodeGeneratorIndex 206 = ![266, 105, 124, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 206 = Subgroup.closure ({word 266, word 105, word 124, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 206)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 207 := rfl

private theorem nodeClosure_eq_207 : nodeClosure 207 = smallEvenDescentNode 208 := by
  have hi : nodeGeneratorIndex 207 = ![266, 36, 124, 119, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 207 = Subgroup.closure ({word 266, word 36, word 124, word 119, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 207)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3, root 4 * root 6 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 208 := rfl

private theorem nodeClosure_eq_208 : nodeClosure 208 = smallEvenDescentNode 209 := by
  have hi : nodeGeneratorIndex 208 = ![312, 34, 113, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 208 = Subgroup.closure ({word 312, word 34, word 113, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 208)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 209 := rfl

private theorem nodeClosure_eq_209 : nodeClosure 209 = smallEvenDescentNode 210 := by
  have hi : nodeGeneratorIndex 209 = ![167, 194, 19, 13, 7, 2, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 209 = Subgroup.closure ({word 167, word 194, word 19, word 13, word 7, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 209)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 7 * root 8 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 210 := rfl

private theorem nodeClosure_eq_210 : nodeClosure 210 = smallEvenDescentNode 211 := by
  have hi : nodeGeneratorIndex 210 = ![167, 171, 19, 13, 7, 2, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 210 = Subgroup.closure ({word 167, word 171, word 19, word 13, word 7, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 210)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 3 * root 5 * root 6 * root 7, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 7 * root 8 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 211 := rfl

private theorem nodeClosure_eq_211 : nodeClosure 211 = smallEvenDescentNode 212 := by
  have hi : nodeGeneratorIndex 211 = ![44, 250, 34, 124, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 211 = Subgroup.closure ({word 44, word 250, word 34, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 211)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 212 := rfl

private theorem nodeClosure_eq_212 : nodeClosure 212 = smallEvenDescentNode 213 := by
  have hi : nodeGeneratorIndex 212 = ![44, 250, 34, 113, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 212 = Subgroup.closure ({word 44, word 250, word 34, word 113, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 212)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 213 := rfl

private theorem nodeClosure_eq_213 : nodeClosure 213 = smallEvenDescentNode 214 := by
  have hi : nodeGeneratorIndex 213 = ![44, 250, 34, 24, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 213 = Subgroup.closure ({word 44, word 250, word 34, word 24, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 213)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 214 := rfl

private theorem nodeClosure_eq_214 : nodeClosure 214 = smallEvenDescentNode 215 := by
  have hi : nodeGeneratorIndex 214 = ![44, 250, 105, 124, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 214 = Subgroup.closure ({word 44, word 250, word 105, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 214)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 215 := rfl

private theorem nodeClosure_eq_215 : nodeClosure 215 = smallEvenDescentNode 216 := by
  have hi : nodeGeneratorIndex 215 = ![44, 250, 110, 113, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 215 = Subgroup.closure ({word 44, word 250, word 110, word 113, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 215)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 2 * root 3 * root 5 * root 6 * root 9, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 216 := rfl

private theorem nodeClosure_eq_216 : nodeClosure 216 = smallEvenDescentNode 217 := by
  have hi : nodeGeneratorIndex 216 = ![44, 328, 34, 124, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 216 = Subgroup.closure ({word 44, word 328, word 34, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 216)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 217 := rfl

private theorem nodeClosure_eq_217 : nodeClosure 217 = smallEvenDescentNode 218 := by
  have hi : nodeGeneratorIndex 217 = ![44, 338, 34, 113, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 217 = Subgroup.closure ({word 44, word 338, word 34, word 113, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 217)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 218 := rfl

private theorem nodeClosure_eq_218 : nodeClosure 218 = smallEvenDescentNode 219 := by
  have hi : nodeGeneratorIndex 218 = ![44, 328, 34, 24, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 218 = Subgroup.closure ({word 44, word 328, word 34, word 24, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 218)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 219 := rfl

private theorem nodeClosure_eq_219 : nodeClosure 219 = smallEvenDescentNode 220 := by
  have hi : nodeGeneratorIndex 219 = ![44, 328, 105, 124, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 219 = Subgroup.closure ({word 44, word 328, word 105, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 219)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 220 := rfl

private theorem nodeClosure_eq_220 : nodeClosure 220 = smallEvenDescentNode 221 := by
  have hi : nodeGeneratorIndex 220 = ![44, 338, 110, 113, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 220 = Subgroup.closure ({word 44, word 338, word 110, word 113, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 220)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 5 * root 6 * root 9, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 221 := rfl

private theorem nodeClosure_eq_221 : nodeClosure 221 = smallEvenDescentNode 222 := by
  have hi : nodeGeneratorIndex 221 = ![92, 250, 34, 124, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 221 = Subgroup.closure ({word 92, word 250, word 34, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 221)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 222 := rfl

private theorem nodeClosure_eq_222 : nodeClosure 222 = smallEvenDescentNode 223 := by
  have hi : nodeGeneratorIndex 222 = ![100, 250, 34, 113, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 222 = Subgroup.closure ({word 100, word 250, word 34, word 113, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 222)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 223 := rfl

private theorem nodeClosure_eq_223 : nodeClosure 223 = smallEvenDescentNode 224 := by
  have hi : nodeGeneratorIndex 223 = ![92, 250, 34, 24, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 223 = Subgroup.closure ({word 92, word 250, word 34, word 24, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 223)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 224 := rfl

private theorem nodeClosure_eq_224 : nodeClosure 224 = smallEvenDescentNode 225 := by
  have hi : nodeGeneratorIndex 224 = ![92, 250, 105, 124, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 224 = Subgroup.closure ({word 92, word 250, word 105, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 224)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 225 := rfl

private theorem nodeClosure_eq_225 : nodeClosure 225 = smallEvenDescentNode 226 := by
  have hi : nodeGeneratorIndex 225 = ![100, 250, 110, 113, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 225 = Subgroup.closure ({word 100, word 250, word 110, word 113, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 225)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 5 * root 6 * root 9, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 226 := rfl

private theorem nodeClosure_eq_226 : nodeClosure 226 = smallEvenDescentNode 227 := by
  have hi : nodeGeneratorIndex 226 = ![92, 328, 34, 124, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 226 = Subgroup.closure ({word 92, word 328, word 34, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 226)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 227 := rfl

private theorem nodeClosure_eq_227 : nodeClosure 227 = smallEvenDescentNode 228 := by
  have hi : nodeGeneratorIndex 227 = ![100, 338, 34, 113, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 227 = Subgroup.closure ({word 100, word 338, word 34, word 113, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 227)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 228 := rfl

private theorem nodeClosure_eq_228 : nodeClosure 228 = smallEvenDescentNode 229 := by
  have hi : nodeGeneratorIndex 228 = ![92, 328, 34, 24, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 228 = Subgroup.closure ({word 92, word 328, word 34, word 24, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 228)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 229 := rfl

private theorem nodeClosure_eq_229 : nodeClosure 229 = smallEvenDescentNode 230 := by
  have hi : nodeGeneratorIndex 229 = ![92, 328, 105, 124, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 229 = Subgroup.closure ({word 92, word 328, word 105, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 229)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 230 := rfl

private theorem nodeClosure_eq_230 : nodeClosure 230 = smallEvenDescentNode 231 := by
  have hi : nodeGeneratorIndex 230 = ![44, 250, 34, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 230 = Subgroup.closure ({word 44, word 250, word 34, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 230)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 4 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 231 := rfl

private theorem nodeClosure_eq_231 : nodeClosure 231 = smallEvenDescentNode 232 := by
  have hi : nodeGeneratorIndex 231 = ![44, 250, 36, 121, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 231 = Subgroup.closure ({word 44, word 250, word 36, word 121, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 231)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 4 * root 6 * root 9, root 2 * root 3 * root 4 * root 5 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 232 := rfl

private theorem nodeClosure_eq_232 : nodeClosure 232 = smallEvenDescentNode 233 := by
  have hi : nodeGeneratorIndex 232 = ![44, 254, 34, 124, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 232 = Subgroup.closure ({word 44, word 254, word 34, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 232)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 233 := rfl

private theorem nodeClosure_eq_233 : nodeClosure 233 = smallEvenDescentNode 234 := by
  have hi : nodeGeneratorIndex 233 = ![44, 338, 34, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 233 = Subgroup.closure ({word 44, word 338, word 34, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 233)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 234 := rfl

private theorem nodeClosure_eq_234 : nodeClosure 234 = smallEvenDescentNode 235 := by
  have hi : nodeGeneratorIndex 234 = ![49, 250, 34, 124, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 234 = Subgroup.closure ({word 49, word 250, word 34, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 234)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 235 := rfl

private theorem nodeClosure_eq_235 : nodeClosure 235 = smallEvenDescentNode 236 := by
  have hi : nodeGeneratorIndex 235 = ![100, 250, 34, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 235 = Subgroup.closure ({word 100, word 250, word 34, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 235)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2, root 4 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 236 := rfl

private theorem nodeClosure_eq_236 : nodeClosure 236 = smallEvenDescentNode 237 := by
  have hi : nodeGeneratorIndex 236 = ![49, 254, 34, 124, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 236 = Subgroup.closure ({word 49, word 254, word 34, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 236)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 237 := rfl

private theorem nodeClosure_eq_237 : nodeClosure 237 = smallEvenDescentNode 238 := by
  have hi : nodeGeneratorIndex 237 = ![100, 338, 34, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 237 = Subgroup.closure ({word 100, word 338, word 34, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 237)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 238 := rfl

private theorem nodeClosure_eq_238 : nodeClosure 238 = smallEvenDescentNode 239 := by
  have hi : nodeGeneratorIndex 238 = ![44, 250, 36, 119, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 238 = Subgroup.closure ({word 44, word 250, word 36, word 119, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 238)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 4 * root 6 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 239 := rfl

private theorem nodeClosure_eq_239 : nodeClosure 239 = smallEvenDescentNode 240 := by
  have hi : nodeGeneratorIndex 239 = ![44, 254, 34, 113, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 239 = Subgroup.closure ({word 44, word 254, word 34, word 113, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 239)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 240 := rfl

private theorem nodeClosure_eq_240 : nodeClosure 240 = smallEvenDescentNode 241 := by
  have hi : nodeGeneratorIndex 240 = ![44, 328, 34, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 240 = Subgroup.closure ({word 44, word 328, word 34, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 240)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 241 := rfl

private theorem nodeClosure_eq_241 : nodeClosure 241 = smallEvenDescentNode 242 := by
  have hi : nodeGeneratorIndex 241 = ![49, 250, 34, 113, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 241 = Subgroup.closure ({word 49, word 250, word 34, word 113, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 241)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 242 := rfl

private theorem nodeClosure_eq_242 : nodeClosure 242 = smallEvenDescentNode 243 := by
  have hi : nodeGeneratorIndex 242 = ![49, 254, 34, 113, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 242 = Subgroup.closure ({word 49, word 254, word 34, word 113, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 242)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 243 := rfl

private theorem nodeClosure_eq_243 : nodeClosure 243 = smallEvenDescentNode 244 := by
  have hi : nodeGeneratorIndex 243 = ![92, 328, 34, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 243 = Subgroup.closure ({word 92, word 328, word 34, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 243)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 244 := rfl

private theorem nodeClosure_eq_244 : nodeClosure 244 = smallEvenDescentNode 245 := by
  have hi : nodeGeneratorIndex 244 = ![44, 250, 43, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 244 = Subgroup.closure ({word 44, word 250, word 43, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 244)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 245 := rfl

private theorem nodeClosure_eq_245 : nodeClosure 245 = smallEvenDescentNode 246 := by
  have hi : nodeGeneratorIndex 245 = ![44, 250, 36, 21, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 245 = Subgroup.closure ({word 44, word 250, word 36, word 21, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 245)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 4 * root 6 * root 9, root 5 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 246 := rfl

private theorem nodeClosure_eq_246 : nodeClosure 246 = smallEvenDescentNode 247 := by
  have hi : nodeGeneratorIndex 246 = ![44, 254, 34, 24, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 246 = Subgroup.closure ({word 44, word 254, word 34, word 24, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 246)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 247 := rfl

private theorem nodeClosure_eq_247 : nodeClosure 247 = smallEvenDescentNode 248 := by
  have hi : nodeGeneratorIndex 247 = ![44, 258, 34, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 247 = Subgroup.closure ({word 44, word 258, word 34, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 247)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 5 * root 6 * root 9, root 4 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 248 := rfl

private theorem nodeClosure_eq_248 : nodeClosure 248 = smallEvenDescentNode 249 := by
  have hi : nodeGeneratorIndex 248 = ![49, 250, 34, 24, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 248 = Subgroup.closure ({word 49, word 250, word 34, word 24, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 248)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 249 := rfl

private theorem nodeClosure_eq_249 : nodeClosure 249 = smallEvenDescentNode 250 := by
  have hi : nodeGeneratorIndex 249 = ![49, 254, 34, 24, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 249 = Subgroup.closure ({word 49, word 254, word 34, word 24, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 249)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 250 := rfl

private theorem nodeClosure_eq_250 : nodeClosure 250 = smallEvenDescentNode 251 := by
  have hi : nodeGeneratorIndex 250 = ![44, 254, 105, 124, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 250 = Subgroup.closure ({word 44, word 254, word 105, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 250)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 251 := rfl

private theorem nodeClosure_eq_251 : nodeClosure 251 = smallEvenDescentNode 252 := by
  have hi : nodeGeneratorIndex 251 = ![44, 254, 106, 124, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 251 = Subgroup.closure ({word 44, word 254, word 106, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 251)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 6 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 252 := rfl

private theorem nodeClosure_eq_252 : nodeClosure 252 = smallEvenDescentNode 253 := by
  have hi : nodeGeneratorIndex 252 = ![44, 254, 106, 121, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 252 = Subgroup.closure ({word 44, word 254, word 106, word 121, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 252)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 6 * root 8, root 2 * root 3 * root 4 * root 5 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 253 := rfl

private theorem nodeClosure_eq_253 : nodeClosure 253 = smallEvenDescentNode 254 := by
  have hi : nodeGeneratorIndex 253 = ![49, 250, 105, 121, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 253 = Subgroup.closure ({word 49, word 250, word 105, word 121, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 253)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 254 := rfl

private theorem nodeClosure_eq_254 : nodeClosure 254 = smallEvenDescentNode 255 := by
  have hi : nodeGeneratorIndex 254 = ![49, 250, 106, 124, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 254 = Subgroup.closure ({word 49, word 250, word 106, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 254)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 6 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 255 := rfl

private theorem nodeClosure_eq_255 : nodeClosure 255 = smallEvenDescentNode 256 := by
  have hi : nodeGeneratorIndex 255 = ![100, 250, 43, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 255 = Subgroup.closure ({word 100, word 250, word 43, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 255)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 256 := rfl

private theorem nodeClosure_eq_256 : nodeClosure 256 = smallEvenDescentNode 257 := by
  have hi : nodeGeneratorIndex 256 = ![49, 250, 106, 121, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 256 = Subgroup.closure ({word 49, word 250, word 106, word 121, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 256)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 6 * root 8, root 2 * root 3 * root 4 * root 5 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 257 := rfl

private theorem nodeClosure_eq_257 : nodeClosure 257 = smallEvenDescentNode 258 := by
  have hi : nodeGeneratorIndex 257 = ![49, 254, 105, 124, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 257 = Subgroup.closure ({word 49, word 254, word 105, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 257)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 258 := rfl

private theorem nodeClosure_eq_258 : nodeClosure 258 = smallEvenDescentNode 259 := by
  have hi : nodeGeneratorIndex 258 = ![49, 254, 105, 121, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 258 = Subgroup.closure ({word 49, word 254, word 105, word 121, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 258)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 259 := rfl

private theorem nodeClosure_eq_259 : nodeClosure 259 = smallEvenDescentNode 260 := by
  have hi : nodeGeneratorIndex 259 = ![49, 254, 106, 124, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 259 = Subgroup.closure ({word 49, word 254, word 106, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 259)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 6 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 260 := rfl

private theorem nodeClosure_eq_260 : nodeClosure 260 = smallEvenDescentNode 261 := by
  have hi : nodeGeneratorIndex 260 = ![100, 338, 43, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 260 = Subgroup.closure ({word 100, word 338, word 43, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 260)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 261 := rfl

private theorem nodeClosure_eq_261 : nodeClosure 261 = smallEvenDescentNode 262 := by
  have hi : nodeGeneratorIndex 261 = ![44, 330, 36, 124, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 261 = Subgroup.closure ({word 44, word 330, word 36, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 261)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 4 * root 6 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 262 := rfl

private theorem nodeClosure_eq_262 : nodeClosure 262 = smallEvenDescentNode 263 := by
  have hi : nodeGeneratorIndex 262 = ![100, 250, 36, 119, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 262 = Subgroup.closure ({word 100, word 250, word 36, word 119, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 262)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2, root 4 * root 6 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 263 := rfl

private theorem nodeClosure_eq_263 : nodeClosure 263 = smallEvenDescentNode 264 := by
  have hi : nodeGeneratorIndex 263 = ![93, 250, 36, 21, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 263 = Subgroup.closure ({word 93, word 250, word 36, word 21, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 263)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 6, rootOne ^ 2, root 4 * root 6 * root 9, root 5 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 264 := rfl

private theorem nodeClosure_eq_264 : nodeClosure 264 = smallEvenDescentNode 265 := by
  have hi : nodeGeneratorIndex 264 = ![93, 330, 36, 124, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 264 = Subgroup.closure ({word 93, word 330, word 36, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 264)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 6, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 4 * root 6 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 265 := rfl

private theorem nodeClosure_eq_265 : nodeClosure 265 = smallEvenDescentNode 266 := by
  have hi : nodeGeneratorIndex 265 = ![44, 332, 36, 113, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 265 = Subgroup.closure ({word 44, word 332, word 36, word 113, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 265)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 8, root 4 * root 6 * root 9, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 266 := rfl

private theorem nodeClosure_eq_266 : nodeClosure 266 = smallEvenDescentNode 267 := by
  have hi : nodeGeneratorIndex 266 = ![92, 328, 36, 22, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 266 = Subgroup.closure ({word 92, word 328, word 36, word 22, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 266)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 6 * root 9, root 5 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 267 := rfl

private theorem nodeClosure_eq_267 : nodeClosure 267 = smallEvenDescentNode 268 := by
  have hi : nodeGeneratorIndex 267 = ![100, 328, 34, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 267 = Subgroup.closure ({word 100, word 328, word 34, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 267)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 268 := rfl

private theorem nodeClosure_eq_268 : nodeClosure 268 = smallEvenDescentNode 269 := by
  have hi : nodeGeneratorIndex 268 = ![131, 116, 17, 15, 5, 2, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 268 = Subgroup.closure ({word 131, word 116, word 17, word 15, word 5, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 268)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 1 * root 5 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 7, root 5 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 269 := rfl

private theorem nodeClosure_eq_269 : nodeClosure 269 = smallEvenDescentNode 270 := by
  have hi : nodeGeneratorIndex 269 = ![131, 34, 17, 15, 5, 2, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 269 = Subgroup.closure ({word 131, word 34, word 17, word 15, word 5, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 269)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 1 * root 5 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 5 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 270 := rfl

private theorem nodeClosure_eq_270 : nodeClosure 270 = smallEvenDescentNode 271 := by
  have hi : nodeGeneratorIndex 270 = ![44, 141, 18, 10, 4, 2, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 270 = Subgroup.closure ({word 44, word 141, word 18, word 10, word 4, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 270)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8, root 6 * root 8, root 7, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 271 := rfl

private theorem nodeClosure_eq_271 : nodeClosure 271 = smallEvenDescentNode 272 := by
  have hi : nodeGeneratorIndex 271 = ![44, 148, 18, 10, 4, 2, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 271 = Subgroup.closure ({word 44, word 148, word 18, word 10, word 4, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 271)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 5 * root 8, root 6 * root 8, root 7, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 272 := rfl

private theorem nodeClosure_eq_272 : nodeClosure 272 = smallEvenDescentNode 273 := by
  have hi : nodeGeneratorIndex 272 = ![90, 141, 18, 10, 4, 2, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 272 = Subgroup.closure ({word 90, word 141, word 18, word 10, word 4, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 272)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8, root 6 * root 8, root 7, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 273 := rfl

private theorem nodeClosure_eq_273 : nodeClosure 273 = smallEvenDescentNode 274 := by
  have hi : nodeGeneratorIndex 273 = ![44, 141, 34, 18, 7, 2, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 273 = Subgroup.closure ({word 44, word 141, word 34, word 18, word 7, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 273)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 5 * root 8, root 7 * root 8 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 274 := rfl

private theorem nodeClosure_eq_274 : nodeClosure 274 = smallEvenDescentNode 275 := by
  have hi : nodeGeneratorIndex 274 = ![44, 141, 37, 18, 7, 2, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 274 = Subgroup.closure ({word 44, word 141, word 37, word 18, word 7, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 274)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 6 * root 7, root 5 * root 8, root 7 * root 8 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 275 := rfl

private theorem nodeClosure_eq_275 : nodeClosure 275 = smallEvenDescentNode 276 := by
  have hi : nodeGeneratorIndex 275 = ![73, 141, 18, 10, 4, 2, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 275 = Subgroup.closure ({word 73, word 141, word 18, word 10, word 4, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 275)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 7, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8, root 6 * root 8, root 7, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 276 := rfl

private theorem nodeClosure_eq_276 : nodeClosure 276 = smallEvenDescentNode 277 := by
  have hi : nodeGeneratorIndex 276 = ![340, 116, 38, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 276 = Subgroup.closure ({word 340, word 116, word 38, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 276)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 1 * root 5 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 5, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 277 := rfl

private theorem nodeClosure_eq_277 : nodeClosure 277 = smallEvenDescentNode 278 := by
  have hi : nodeGeneratorIndex 277 = ![340, 34, 38, 15, 5, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 277 = Subgroup.closure ({word 340, word 34, word 38, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 277)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 1 * root 5 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 4 * root 5, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 278 := rfl

private theorem nodeClosure_eq_278 : nodeClosure 278 = smallEvenDescentNode 279 := by
  have hi : nodeGeneratorIndex 278 = ![44, 348, 40, 10, 4, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 278 = Subgroup.closure ({word 44, word 348, word 40, word 10, word 4, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 278)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 5 * root 8 * root 9, root 6 * root 8, root 7, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 279 := rfl

private theorem nodeClosure_eq_279 : nodeClosure 279 = smallEvenDescentNode 280 := by
  have hi : nodeGeneratorIndex 279 = ![44, 351, 40, 10, 4, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 279 = Subgroup.closure ({word 44, word 351, word 40, word 10, word 4, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 279)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 4 * root 5 * root 8 * root 9, root 6 * root 8, root 7, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 280 := rfl

private theorem nodeClosure_eq_280 : nodeClosure 280 = smallEvenDescentNode 281 := by
  have hi : nodeGeneratorIndex 280 = ![90, 348, 40, 10, 4, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 280 = Subgroup.closure ({word 90, word 348, word 40, word 10, word 4, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 280)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 5 * root 8 * root 9, root 6 * root 8, root 7, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 281 := rfl

private theorem nodeClosure_eq_281 : nodeClosure 281 = smallEvenDescentNode 282 := by
  have hi : nodeGeneratorIndex 281 = ![44, 348, 34, 40, 7, 2, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 281 = Subgroup.closure ({word 44, word 348, word 34, word 40, word 7, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 281)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 4 * root 5 * root 8 * root 9, root 7 * root 8 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 282 := rfl

private theorem nodeClosure_eq_282 : nodeClosure 282 = smallEvenDescentNode 283 := by
  have hi : nodeGeneratorIndex 282 = ![46, 348, 34, 40, 7, 2, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 282 = Subgroup.closure ({word 46, word 348, word 34, word 40, word 7, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 282)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 8, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 4 * root 5 * root 8 * root 9, root 7 * root 8 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 283 := rfl

private theorem nodeClosure_eq_283 : nodeClosure 283 = smallEvenDescentNode 284 := by
  have hi : nodeGeneratorIndex 283 = ![131, 254, 17, 35, 2, 7, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 283 = Subgroup.closure ({word 131, word 254, word 17, word 35, word 2, word 7, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 283)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 1 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 5 * root 9, root 4 * root 7 * root 8 * root 9, root 8, root 7 * root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 284 := rfl

private theorem nodeClosure_eq_284 : nodeClosure 284 = smallEvenDescentNode 285 := by
  have hi : nodeGeneratorIndex 284 = ![157, 235, 2, 22, 8, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 284 = Subgroup.closure ({word 157, word 235, word 2, word 22, word 8, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 284)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 285 := rfl

private theorem nodeClosure_eq_285 : nodeClosure 285 = smallEvenDescentNode 286 := by
  have hi : nodeGeneratorIndex 285 = ![157, 213, 2, 22, 8, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 285 = Subgroup.closure ({word 157, word 213, word 2, word 22, word 8, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 285)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 1 * root 4 * root 6, root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 286 := rfl

private theorem nodeClosure_eq_286 : nodeClosure 286 = smallEvenDescentNode 287 := by
  have hi : nodeGeneratorIndex 286 = ![200, 235, 2, 22, 8, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 286 = Subgroup.closure ({word 200, word 235, word 2, word 22, word 8, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 286)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 287 := rfl

private theorem nodeClosure_eq_287 : nodeClosure 287 = smallEvenDescentNode 288 := by
  have hi : nodeGeneratorIndex 287 = ![200, 213, 2, 22, 8, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 287 = Subgroup.closure ({word 200, word 213, word 2, word 22, word 8, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 287)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 1 * root 4 * root 6, root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 288 := rfl

private theorem nodeClosure_eq_288 : nodeClosure 288 = smallEvenDescentNode 289 := by
  have hi : nodeGeneratorIndex 288 = ![157, 235, 34, 22, 8, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 288 = Subgroup.closure ({word 157, word 235, word 34, word 22, word 8, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 288)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 4 * root 7 * root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 289 := rfl

private theorem nodeClosure_eq_289 : nodeClosure 289 = smallEvenDescentNode 290 := by
  have hi : nodeGeneratorIndex 289 = ![157, 234, 34, 22, 8, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 289 = Subgroup.closure ({word 157, word 234, word 34, word 22, word 8, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 289)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 1 * root 2 * root 3 * root 6, root 4 * root 7 * root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 290 := rfl

private theorem nodeClosure_eq_290 : nodeClosure 290 = smallEvenDescentNode 291 := by
  have hi : nodeGeneratorIndex 290 = ![167, 235, 2, 22, 8, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 290 = Subgroup.closure ({word 167, word 235, word 2, word 22, word 8, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 290)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 291 := rfl

private theorem nodeClosure_eq_291 : nodeClosure 291 = smallEvenDescentNode 292 := by
  have hi : nodeGeneratorIndex 291 = ![167, 246, 2, 22, 8, 5, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 291 = Subgroup.closure ({word 167, word 246, word 2, word 22, word 8, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 291)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 7, root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 292 := rfl

private theorem nodeClosure_eq_292 : nodeClosure 292 = smallEvenDescentNode 293 := by
  have hi : nodeGeneratorIndex 292 = ![157, 235, 103, 22, 8, 7, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 292 = Subgroup.closure ({word 157, word 235, word 103, word 22, word 8, word 7, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 292)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 2 * root 3 * root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 293 := rfl

private theorem nodeClosure_eq_293 : nodeClosure 293 = smallEvenDescentNode 294 := by
  have hi : nodeGeneratorIndex 293 = ![157, 235, 102, 22, 8, 7, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 293 = Subgroup.closure ({word 157, word 235, word 102, word 22, word 8, word 7, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 293)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 2 * root 3, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 294 := rfl

private theorem nodeClosure_eq_294 : nodeClosure 294 = smallEvenDescentNode 295 := by
  have hi : nodeGeneratorIndex 294 = ![196, 235, 2, 22, 8, 7, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 294 = Subgroup.closure ({word 196, word 235, word 2, word 22, word 8, word 7, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 294)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 3 * root 8, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 295 := rfl

private theorem nodeClosure_eq_295 : nodeClosure 295 = smallEvenDescentNode 296 := by
  have hi : nodeGeneratorIndex 295 = ![167, 213, 2, 25, 12, 6, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 295 = Subgroup.closure ({word 167, word 213, word 2, word 25, word 12, word 6, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 295)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 1 * root 4 * root 6, root 8, root 5 * root 6 * root 8, root 6 * root 7, root 7 * root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 296 := rfl

private theorem nodeClosure_eq_296 : nodeClosure 296 = smallEvenDescentNode 297 := by
  have hi : nodeGeneratorIndex 296 = ![194, 141, 30, 12, 6, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 296 = Subgroup.closure ({word 194, word 141, word 30, word 12, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 296)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 297 := rfl

private theorem nodeClosure_eq_297 : nodeClosure 297 = smallEvenDescentNode 298 := by
  have hi : nodeGeneratorIndex 297 = ![194, 148, 30, 12, 6, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 297 = Subgroup.closure ({word 194, word 148, word 30, word 12, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 297)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 298 := rfl

private theorem nodeClosure_eq_298 : nodeClosure 298 = smallEvenDescentNode 299 := by
  have hi : nodeGeneratorIndex 298 = ![169, 148, 30, 12, 6, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 298 = Subgroup.closure ({word 169, word 148, word 30, word 12, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 298)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 3 * root 5 * root 6 * root 9, root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 299 := rfl

private theorem nodeClosure_eq_299 : nodeClosure 299 = smallEvenDescentNode 300 := by
  have hi : nodeGeneratorIndex 299 = ![182, 144, 30, 12, 6, 3, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 299 = Subgroup.closure ({word 182, word 144, word 30, word 12, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 299)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 5 * root 6 * root 9, root 1 * root 3 * root 4 * root 5 * root 6 * root 8, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 300 := rfl

private theorem nodeClosure_eq_300 : nodeClosure 300 = smallEvenDescentNode 301 := by
  have hi : nodeGeneratorIndex 300 = ![271, 141, 18, 34, 2, 7, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 300 = Subgroup.closure ({word 271, word 141, word 18, word 34, word 2, word 7, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 300)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3 * root 6 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8, root 4 * root 7 * root 8, root 8, root 7 * root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 301 := rfl

private theorem nodeClosure_eq_301 : nodeClosure 301 = smallEvenDescentNode 302 := by
  have hi : nodeGeneratorIndex 301 = ![131, 343, 17, 32, 2, 6, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 301 = Subgroup.closure ({word 131, word 343, word 17, word 32, word 2, word 6, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 301)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 1 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 8, root 5 * root 9, root 4 * root 9, root 8, root 7 * root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 302 := rfl

private theorem nodeClosure_eq_302 : nodeClosure 302 = smallEvenDescentNode 303 := by
  have hi : nodeGeneratorIndex 302 = ![157, 169, 141, 24, 11, 2, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 302 = Subgroup.closure ({word 157, word 169, word 141, word 24, word 11, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 302)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 3 * root 5 * root 6 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 9, root 6 * root 8 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 303 := rfl

private theorem nodeClosure_eq_303 : nodeClosure 303 = smallEvenDescentNode 304 := by
  have hi : nodeGeneratorIndex 303 = ![157, 169, 138, 24, 11, 2, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 303 = Subgroup.closure ({word 157, word 169, word 138, word 24, word 11, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 303)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 3 * root 5 * root 6 * root 9, root 1 * root 3 * root 5 * root 6, root 5 * root 6 * root 9, root 6 * root 8 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 304 := rfl

private theorem nodeClosure_eq_304 : nodeClosure 304 = smallEvenDescentNode 305 := by
  have hi : nodeGeneratorIndex 304 = ![200, 194, 141, 28, 14, 2, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 304 = Subgroup.closure ({word 200, word 194, word 141, word 28, word 14, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 304)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7 * root 9, root 6 * root 7 * root 8, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 305 := rfl

private theorem nodeClosure_eq_305 : nodeClosure 305 = smallEvenDescentNode 306 := by
  have hi : nodeGeneratorIndex 305 = ![200, 191, 141, 28, 14, 2, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 305 = Subgroup.closure ({word 200, word 191, word 141, word 28, word 14, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 305)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7 * root 9, root 6 * root 7 * root 8, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 306 := rfl

private theorem nodeClosure_eq_306 : nodeClosure 306 = smallEvenDescentNode 307 := by
  have hi : nodeGeneratorIndex 306 = ![167, 194, 141, 5, 19, 13, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 306 = Subgroup.closure ({word 167, word 194, word 141, word 5, word 19, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 306)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 307 := rfl

private theorem nodeClosure_eq_307 : nodeClosure 307 = smallEvenDescentNode 308 := by
  have hi : nodeGeneratorIndex 307 = ![167, 194, 141, 3, 19, 13, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 307 = Subgroup.closure ({word 167, word 194, word 141, word 3, word 19, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 307)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 308 := rfl

private theorem nodeClosure_eq_308 : nodeClosure 308 = smallEvenDescentNode 309 := by
  have hi : nodeGeneratorIndex 308 = ![167, 194, 141, 6, 19, 13, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 308 = Subgroup.closure ({word 167, word 194, word 141, word 6, word 19, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 308)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 309 := rfl

private theorem nodeClosure_eq_309 : nodeClosure 309 = smallEvenDescentNode 310 := by
  have hi : nodeGeneratorIndex 309 = ![167, 194, 142, 5, 19, 13, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 309 = Subgroup.closure ({word 167, word 194, word 142, word 5, word 19, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 309)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 8, root 7 * root 9, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 310 := rfl

private theorem nodeClosure_eq_310 : nodeClosure 310 = smallEvenDescentNode 311 := by
  have hi : nodeGeneratorIndex 310 = ![167, 194, 142, 6, 19, 13, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 310 = Subgroup.closure ({word 167, word 194, word 142, word 6, word 19, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 310)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 8, root 7 * root 8, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 311 := rfl

private theorem nodeClosure_eq_311 : nodeClosure 311 = smallEvenDescentNode 312 := by
  have hi : nodeGeneratorIndex 311 = ![167, 191, 141, 3, 19, 13, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 311 = Subgroup.closure ({word 167, word 191, word 141, word 3, word 19, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 311)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 312 := rfl

private theorem nodeClosure_eq_312 : nodeClosure 312 = smallEvenDescentNode 313 := by
  have hi : nodeGeneratorIndex 312 = ![166, 194, 141, 6, 19, 13, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 312 = Subgroup.closure ({word 166, word 194, word 141, word 6, word 19, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 312)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 313 := rfl

private theorem nodeClosure_eq_313 : nodeClosure 313 = smallEvenDescentNode 314 := by
  have hi : nodeGeneratorIndex 313 = ![166, 194, 142, 6, 19, 13, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 313 = Subgroup.closure ({word 166, word 194, word 142, word 6, word 19, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 313)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 8, root 7 * root 8, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 314 := rfl

private theorem nodeClosure_eq_314 : nodeClosure 314 = smallEvenDescentNode 315 := by
  have hi : nodeGeneratorIndex 314 = ![355, 124, 113, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 314 = Subgroup.closure ({word 355, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 314)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 315 := rfl

private theorem nodeClosure_eq_315 : nodeClosure 315 = smallEvenDescentNode 316 := by
  have hi : nodeGeneratorIndex 315 = ![44, 124, 113, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 315 = Subgroup.closure ({word 44, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 315)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 316 := rfl

private theorem nodeClosure_eq_316 : nodeClosure 316 = smallEvenDescentNode 317 := by
  have hi : nodeGeneratorIndex 316 = ![194, 124, 113, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 316 = Subgroup.closure ({word 194, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 316)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 317 := rfl

private theorem nodeClosure_eq_317 : nodeClosure 317 = smallEvenDescentNode 318 := by
  have hi : nodeGeneratorIndex 317 = ![266, 124, 113, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 317 = Subgroup.closure ({word 266, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 317)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 318 := rfl

private theorem nodeClosure_eq_318 : nodeClosure 318 = smallEvenDescentNode 319 := by
  have hi : nodeGeneratorIndex 318 = ![355, 250, 124, 114, 1, 5, 5, 5, 5, 5] := rfl
  calc
    nodeClosure 318 = Subgroup.closure ({word 355, word 250, word 124, word 114, word 1, word 5} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 318)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 3, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 8, root 9, root 7 * root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 319 := rfl

private theorem nodeClosure_eq_319 : nodeClosure 319 = smallEvenDescentNode 320 := by
  have hi : nodeGeneratorIndex 319 = ![157, 355, 113, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 319 = Subgroup.closure ({word 157, word 355, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 319)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 320 := rfl

private theorem nodeClosure_eq_320 : nodeClosure 320 = smallEvenDescentNode 321 := by
  have hi : nodeGeneratorIndex 320 = ![157, 367, 113, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 320 = Subgroup.closure ({word 157, word 367, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 320)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, rootOne ^ 2 * root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 321 := rfl

private theorem nodeClosure_eq_321 : nodeClosure 321 = smallEvenDescentNode 322 := by
  have hi : nodeGeneratorIndex 321 = ![44, 250, 124, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 321 = Subgroup.closure ({word 44, word 250, word 124, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 321)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 322 := rfl

private theorem nodeClosure_eq_322 : nodeClosure 322 = smallEvenDescentNode 323 := by
  have hi : nodeGeneratorIndex 322 = ![44, 250, 113, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 322 = Subgroup.closure ({word 44, word 250, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 322)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 323 := rfl

private theorem nodeClosure_eq_323 : nodeClosure 323 = smallEvenDescentNode 324 := by
  have hi : nodeGeneratorIndex 323 = ![44, 328, 124, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 323 = Subgroup.closure ({word 44, word 328, word 124, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 323)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 324 := rfl

private theorem nodeClosure_eq_324 : nodeClosure 324 = smallEvenDescentNode 325 := by
  have hi : nodeGeneratorIndex 324 = ![44, 338, 113, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 324 = Subgroup.closure ({word 44, word 338, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 324)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 325 := rfl

private theorem nodeClosure_eq_325 : nodeClosure 325 = smallEvenDescentNode 326 := by
  have hi : nodeGeneratorIndex 325 = ![92, 250, 24, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 325 = Subgroup.closure ({word 92, word 250, word 24, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 325)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2, root 5 * root 6 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 326 := rfl

private theorem nodeClosure_eq_326 : nodeClosure 326 = smallEvenDescentNode 327 := by
  have hi : nodeGeneratorIndex 326 = ![49, 124, 113, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 326 = Subgroup.closure ({word 49, word 124, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 326)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 327 := rfl

private theorem nodeClosure_eq_327 : nodeClosure 327 = smallEvenDescentNode 328 := by
  have hi : nodeGeneratorIndex 327 = ![355, 15, 113, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 327 = Subgroup.closure ({word 355, word 15, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 327)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 3, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 328 := rfl

private theorem nodeClosure_eq_328 : nodeClosure 328 = smallEvenDescentNode 329 := by
  have hi : nodeGeneratorIndex 328 = ![355, 122, 113, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 328 = Subgroup.closure ({word 355, word 122, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 328)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 329 := rfl

private theorem nodeClosure_eq_329 : nodeClosure 329 = smallEvenDescentNode 330 := by
  have hi : nodeGeneratorIndex 329 = ![44, 15, 124, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 329 = Subgroup.closure ({word 44, word 15, word 124, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 329)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 330 := rfl

private theorem nodeClosure_eq_330 : nodeClosure 330 = smallEvenDescentNode 331 := by
  have hi : nodeGeneratorIndex 330 = ![44, 15, 113, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 330 = Subgroup.closure ({word 44, word 15, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 330)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 331 := rfl

private theorem nodeClosure_eq_331 : nodeClosure 331 = smallEvenDescentNode 332 := by
  have hi : nodeGeneratorIndex 331 = ![44, 15, 24, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 331 = Subgroup.closure ({word 44, word 15, word 24, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 331)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 332 := rfl

private theorem nodeClosure_eq_332 : nodeClosure 332 = smallEvenDescentNode 333 := by
  have hi : nodeGeneratorIndex 332 = ![44, 120, 124, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 332 = Subgroup.closure ({word 44, word 120, word 124, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 332)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 333 := rfl

private theorem nodeClosure_eq_333 : nodeClosure 333 = smallEvenDescentNode 334 := by
  have hi : nodeGeneratorIndex 333 = ![92, 15, 24, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 333 = Subgroup.closure ({word 92, word 15, word 24, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 333)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 334 := rfl

private theorem nodeClosure_eq_334 : nodeClosure 334 = smallEvenDescentNode 335 := by
  have hi : nodeGeneratorIndex 334 = ![371, 187, 124, 117, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 334 = Subgroup.closure ({word 371, word 187, word 124, word 117, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 334)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 0 * root 2 * root 4 * root 5 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7 * root 8, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 335 := rfl

private theorem nodeClosure_eq_335 : nodeClosure 335 = smallEvenDescentNode 336 := by
  have hi : nodeGeneratorIndex 335 = ![275, 3, 124, 117, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 335 = Subgroup.closure ({word 275, word 3, word 124, word 117, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 335)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3 * root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7 * root 8, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 336 := rfl

private theorem nodeClosure_eq_336 : nodeClosure 336 = smallEvenDescentNode 337 := by
  have hi : nodeGeneratorIndex 336 = ![161, 355, 124, 115, 1, 5, 5, 5, 5, 5] := rfl
  calc
    nodeClosure 336 = Subgroup.closure ({word 161, word 355, word 124, word 115, word 1, word 5} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 336)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 8 * root 9, root 9, root 7 * root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 337 := rfl

private theorem nodeClosure_eq_337 : nodeClosure 337 = smallEvenDescentNode 338 := by
  have hi : nodeGeneratorIndex 337 = ![161, 355, 3, 115, 1, 5, 5, 5, 5, 5] := rfl
  calc
    nodeClosure 337 = Subgroup.closure ({word 161, word 355, word 3, word 115, word 1, word 5} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 337)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 0 * root 3, root 8 * root 9, root 2 * root 3 * root 4 * root 8 * root 9, root 9, root 7 * root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 338 := rfl

private theorem nodeClosure_eq_338 : nodeClosure 338 = smallEvenDescentNode 339 := by
  have hi : nodeGeneratorIndex 338 = ![161, 355, 125, 115, 1, 5, 5, 5, 5, 5] := rfl
  calc
    nodeClosure 338 = Subgroup.closure ({word 161, word 355, word 125, word 115, word 1, word 5} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 338)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 8 * root 9, root 9, root 7 * root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 339 := rfl

private theorem nodeClosure_eq_339 : nodeClosure 339 = smallEvenDescentNode 340 := by
  have hi : nodeGeneratorIndex 339 = ![161, 367, 3, 115, 1, 5, 5, 5, 5, 5] := rfl
  calc
    nodeClosure 339 = Subgroup.closure ({word 161, word 367, word 3, word 115, word 1, word 5} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 339)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 8 * root 9, root 2 * root 3 * root 4 * root 8 * root 9, root 9, root 7 * root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 340 := rfl

private theorem nodeClosure_eq_340 : nodeClosure 340 = smallEvenDescentNode 341 := by
  have hi : nodeGeneratorIndex 340 = ![160, 355, 125, 115, 1, 5, 5, 5, 5, 5] := rfl
  calc
    nodeClosure 340 = Subgroup.closure ({word 160, word 355, word 125, word 115, word 1, word 5} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 340)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 6 * root 7, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 8 * root 9, root 9, root 7 * root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 341 := rfl

private theorem nodeClosure_eq_341 : nodeClosure 341 = smallEvenDescentNode 342 := by
  have hi : nodeGeneratorIndex 341 = ![44, 254, 124, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 341 = Subgroup.closure ({word 44, word 254, word 124, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 341)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 342 := rfl

private theorem nodeClosure_eq_342 : nodeClosure 342 = smallEvenDescentNode 343 := by
  have hi : nodeGeneratorIndex 342 = ![44, 254, 113, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 342 = Subgroup.closure ({word 44, word 254, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 342)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 343 := rfl

private theorem nodeClosure_eq_343 : nodeClosure 343 = smallEvenDescentNode 344 := by
  have hi : nodeGeneratorIndex 343 = ![44, 254, 24, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 343 = Subgroup.closure ({word 44, word 254, word 24, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 343)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 344 := rfl

private theorem nodeClosure_eq_344 : nodeClosure 344 = smallEvenDescentNode 345 := by
  have hi : nodeGeneratorIndex 344 = ![44, 331, 124, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 344 = Subgroup.closure ({word 44, word 331, word 124, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 344)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 345 := rfl

private theorem nodeClosure_eq_345 : nodeClosure 345 = smallEvenDescentNode 346 := by
  have hi : nodeGeneratorIndex 345 = ![44, 333, 113, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 345 = Subgroup.closure ({word 44, word 333, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 345)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 346 := rfl

private theorem nodeClosure_eq_346 : nodeClosure 346 = smallEvenDescentNode 347 := by
  have hi : nodeGeneratorIndex 346 = ![92, 254, 24, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 346 = Subgroup.closure ({word 92, word 254, word 24, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 346)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 347 := rfl

private theorem nodeClosure_eq_347 : nodeClosure 347 = smallEvenDescentNode 348 := by
  have hi : nodeGeneratorIndex 347 = ![49, 250, 124, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 347 = Subgroup.closure ({word 49, word 250, word 124, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 347)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 348 := rfl

private theorem nodeClosure_eq_348 : nodeClosure 348 = smallEvenDescentNode 349 := by
  have hi : nodeGeneratorIndex 348 = ![49, 250, 113, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 348 = Subgroup.closure ({word 49, word 250, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 348)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 349 := rfl

private theorem nodeClosure_eq_349 : nodeClosure 349 = smallEvenDescentNode 350 := by
  have hi : nodeGeneratorIndex 349 = ![49, 250, 24, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 349 = Subgroup.closure ({word 49, word 250, word 24, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 349)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 5 * root 6 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 350 := rfl

private theorem nodeClosure_eq_350 : nodeClosure 350 = smallEvenDescentNode 351 := by
  have hi : nodeGeneratorIndex 350 = ![49, 328, 124, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 350 = Subgroup.closure ({word 49, word 328, word 124, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 350)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 351 := rfl

private theorem nodeClosure_eq_351 : nodeClosure 351 = smallEvenDescentNode 352 := by
  have hi : nodeGeneratorIndex 351 = ![49, 338, 113, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 351 = Subgroup.closure ({word 49, word 338, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 351)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 352 := rfl

private theorem nodeClosure_eq_352 : nodeClosure 352 = smallEvenDescentNode 353 := by
  have hi : nodeGeneratorIndex 352 = ![94, 250, 24, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 352 = Subgroup.closure ({word 94, word 250, word 24, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 352)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 6 * root 9, rootOne ^ 2, root 5 * root 6 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 353 := rfl

private theorem nodeClosure_eq_353 : nodeClosure 353 = smallEvenDescentNode 354 := by
  have hi : nodeGeneratorIndex 353 = ![194, 15, 113, 30, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 353 = Subgroup.closure ({word 194, word 15, word 113, word 30, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 353)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 354 := rfl

private theorem nodeClosure_eq_354 : nodeClosure 354 = smallEvenDescentNode 355 := by
  have hi : nodeGeneratorIndex 354 = ![194, 15, 3, 30, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 354 = Subgroup.closure ({word 194, word 15, word 3, word 30, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 354)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 355 := rfl

private theorem nodeClosure_eq_355 : nodeClosure 355 = smallEvenDescentNode 356 := by
  have hi : nodeGeneratorIndex 355 = ![266, 15, 124, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 355 = Subgroup.closure ({word 266, word 15, word 124, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 355)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 356 := rfl

private theorem nodeClosure_eq_356 : nodeClosure 356 = smallEvenDescentNode 357 := by
  have hi : nodeGeneratorIndex 356 = ![266, 15, 113, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 356 = Subgroup.closure ({word 266, word 15, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 356)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 357 := rfl

private theorem nodeClosure_eq_357 : nodeClosure 357 = smallEvenDescentNode 358 := by
  have hi : nodeGeneratorIndex 357 = ![266, 120, 124, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 357 = Subgroup.closure ({word 266, word 120, word 124, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 357)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3, root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 358 := rfl

private theorem nodeClosure_eq_358 : nodeClosure 358 = smallEvenDescentNode 359 := by
  have hi : nodeGeneratorIndex 358 = ![266, 122, 113, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 358 = Subgroup.closure ({word 266, word 122, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 358)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 359 := rfl

private theorem nodeClosure_eq_359 : nodeClosure 359 = smallEvenDescentNode 360 := by
  have hi : nodeGeneratorIndex 359 = ![266, 120, 24, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 359 = Subgroup.closure ({word 266, word 120, word 24, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 359)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3, root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 360 := rfl

private theorem nodeClosure_eq_360 : nodeClosure 360 = smallEvenDescentNode 361 := by
  have hi : nodeGeneratorIndex 360 = ![312, 15, 113, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 360 = Subgroup.closure ({word 312, word 15, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 360)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 361 := rfl

private theorem nodeClosure_eq_361 : nodeClosure 361 = smallEvenDescentNode 362 := by
  have hi : nodeGeneratorIndex 361 = ![312, 122, 113, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 361 = Subgroup.closure ({word 312, word 122, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 361)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 362 := rfl

private theorem nodeClosure_eq_362 : nodeClosure 362 = smallEvenDescentNode 363 := by
  have hi : nodeGeneratorIndex 362 = ![49, 254, 124, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 362 = Subgroup.closure ({word 49, word 254, word 124, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 362)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 363 := rfl

private theorem nodeClosure_eq_363 : nodeClosure 363 = smallEvenDescentNode 364 := by
  have hi : nodeGeneratorIndex 363 = ![49, 254, 113, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 363 = Subgroup.closure ({word 49, word 254, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 363)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 364 := rfl

private theorem nodeClosure_eq_364 : nodeClosure 364 = smallEvenDescentNode 365 := by
  have hi : nodeGeneratorIndex 364 = ![49, 254, 24, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 364 = Subgroup.closure ({word 49, word 254, word 24, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 364)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 365 := rfl

private theorem nodeClosure_eq_365 : nodeClosure 365 = smallEvenDescentNode 366 := by
  have hi : nodeGeneratorIndex 365 = ![49, 331, 124, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 365 = Subgroup.closure ({word 49, word 331, word 124, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 365)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 366 := rfl

private theorem nodeClosure_eq_366 : nodeClosure 366 = smallEvenDescentNode 367 := by
  have hi : nodeGeneratorIndex 366 = ![49, 333, 113, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 366 = Subgroup.closure ({word 49, word 333, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 366)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 367 := rfl

private theorem nodeClosure_eq_367 : nodeClosure 367 = smallEvenDescentNode 368 := by
  have hi : nodeGeneratorIndex 367 = ![94, 254, 24, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 367 = Subgroup.closure ({word 94, word 254, word 24, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 367)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 6 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 368 := rfl

private theorem nodeClosure_eq_368 : nodeClosure 368 = smallEvenDescentNode 369 := by
  have hi : nodeGeneratorIndex 368 = ![44, 338, 15, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 368 = Subgroup.closure ({word 44, word 338, word 15, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 368)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 369 := rfl

private theorem nodeClosure_eq_369 : nodeClosure 369 = smallEvenDescentNode 370 := by
  have hi : nodeGeneratorIndex 369 = ![44, 338, 122, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 369 = Subgroup.closure ({word 44, word 338, word 122, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 369)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 370 := rfl

private theorem nodeClosure_eq_370 : nodeClosure 370 = smallEvenDescentNode 371 := by
  have hi : nodeGeneratorIndex 370 = ![100, 250, 15, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 370 = Subgroup.closure ({word 100, word 250, word 15, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 370)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2, root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 371 := rfl

private theorem nodeClosure_eq_371 : nodeClosure 371 = smallEvenDescentNode 372 := by
  have hi : nodeGeneratorIndex 371 = ![100, 250, 122, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 371 = Subgroup.closure ({word 100, word 250, word 122, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 371)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 372 := rfl

private theorem nodeClosure_eq_372 : nodeClosure 372 = smallEvenDescentNode 373 := by
  have hi : nodeGeneratorIndex 372 = ![100, 338, 15, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 372 = Subgroup.closure ({word 100, word 338, word 15, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 372)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 373 := rfl

private theorem nodeClosure_eq_373 : nodeClosure 373 = smallEvenDescentNode 374 := by
  have hi : nodeGeneratorIndex 373 = ![100, 338, 122, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 373 = Subgroup.closure ({word 100, word 338, word 122, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 373)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 374 := rfl

private theorem nodeClosure_eq_374 : nodeClosure 374 = smallEvenDescentNode 375 := by
  have hi : nodeGeneratorIndex 374 = ![44, 328, 15, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 374 = Subgroup.closure ({word 44, word 328, word 15, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 374)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 375 := rfl

private theorem nodeClosure_eq_375 : nodeClosure 375 = smallEvenDescentNode 376 := by
  have hi : nodeGeneratorIndex 375 = ![44, 328, 120, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 375 = Subgroup.closure ({word 44, word 328, word 120, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 375)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 376 := rfl

private theorem nodeClosure_eq_376 : nodeClosure 376 = smallEvenDescentNode 377 := by
  have hi : nodeGeneratorIndex 376 = ![92, 250, 120, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 376 = Subgroup.closure ({word 92, word 250, word 120, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 376)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 377 := rfl

private theorem nodeClosure_eq_377 : nodeClosure 377 = smallEvenDescentNode 378 := by
  have hi : nodeGeneratorIndex 377 = ![92, 328, 15, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 377 = Subgroup.closure ({word 92, word 328, word 15, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 377)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 378 := rfl

private theorem nodeClosure_eq_378 : nodeClosure 378 = smallEvenDescentNode 379 := by
  have hi : nodeGeneratorIndex 378 = ![92, 328, 120, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 378 = Subgroup.closure ({word 92, word 328, word 120, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 378)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 379 := rfl

private theorem nodeClosure_eq_379 : nodeClosure 379 = smallEvenDescentNode 380 := by
  have hi : nodeGeneratorIndex 379 = ![44, 250, 21, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 379 = Subgroup.closure ({word 44, word 250, word 21, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 379)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 5 * root 7 * root 8, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 380 := rfl

private theorem nodeClosure_eq_380 : nodeClosure 380 = smallEvenDescentNode 381 := by
  have hi : nodeGeneratorIndex 380 = ![44, 258, 15, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 380 = Subgroup.closure ({word 44, word 258, word 15, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 380)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 5 * root 6 * root 9, root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 381 := rfl

private theorem nodeClosure_eq_381 : nodeClosure 381 = smallEvenDescentNode 382 := by
  have hi : nodeGeneratorIndex 381 = ![44, 258, 21, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 381 = Subgroup.closure ({word 44, word 258, word 21, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 381)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 5 * root 6 * root 9, root 5 * root 7 * root 8, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 382 := rfl

private theorem nodeClosure_eq_382 : nodeClosure 382 = smallEvenDescentNode 383 := by
  have hi : nodeGeneratorIndex 382 = ![54, 250, 21, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 382 = Subgroup.closure ({word 54, word 250, word 21, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 382)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 5 * root 6 * root 9, rootOne ^ 2, root 5 * root 7 * root 8, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 383 := rfl

private theorem nodeClosure_eq_383 : nodeClosure 383 = smallEvenDescentNode 384 := by
  have hi : nodeGeneratorIndex 383 = ![54, 258, 21, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 383 = Subgroup.closure ({word 54, word 258, word 21, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 383)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 5 * root 6 * root 9, rootOne ^ 2 * root 5 * root 6 * root 9, root 5 * root 7 * root 8, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 384 := rfl

private theorem nodeClosure_eq_384 : nodeClosure 384 = smallEvenDescentNode 385 := by
  have hi : nodeGeneratorIndex 384 = ![44, 338, 120, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 384 = Subgroup.closure ({word 44, word 338, word 120, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 384)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 385 := rfl

private theorem nodeClosure_eq_385 : nodeClosure 385 = smallEvenDescentNode 386 := by
  have hi : nodeGeneratorIndex 385 = ![100, 250, 120, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 385 = Subgroup.closure ({word 100, word 250, word 120, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 385)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 386 := rfl

private theorem nodeClosure_eq_386 : nodeClosure 386 = smallEvenDescentNode 387 := by
  have hi : nodeGeneratorIndex 386 = ![44, 328, 122, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 386 = Subgroup.closure ({word 44, word 328, word 122, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 386)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 387 := rfl

private theorem nodeClosure_eq_387 : nodeClosure 387 = smallEvenDescentNode 388 := by
  have hi : nodeGeneratorIndex 387 = ![92, 328, 122, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 387 = Subgroup.closure ({word 92, word 328, word 122, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 387)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 388 := rfl

private theorem nodeClosure_eq_388 : nodeClosure 388 = smallEvenDescentNode 389 := by
  have hi : nodeGeneratorIndex 388 = ![44, 258, 120, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 388 = Subgroup.closure ({word 44, word 258, word 120, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 388)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 5 * root 6 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 389 := rfl

private theorem nodeClosure_eq_389 : nodeClosure 389 = smallEvenDescentNode 390 := by
  have hi : nodeGeneratorIndex 389 = ![44, 258, 123, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 389 = Subgroup.closure ({word 44, word 258, word 123, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 389)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 5 * root 6 * root 9, root 2 * root 3 * root 4 * root 5 * root 7 * root 8, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 390 := rfl

private theorem nodeClosure_eq_390 : nodeClosure 390 = smallEvenDescentNode 391 := by
  have hi : nodeGeneratorIndex 390 = ![100, 328, 15, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 390 = Subgroup.closure ({word 100, word 328, word 15, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 390)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 391 := rfl

private theorem nodeClosure_eq_391 : nodeClosure 391 = smallEvenDescentNode 392 := by
  have hi : nodeGeneratorIndex 391 = ![100, 328, 122, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 391 = Subgroup.closure ({word 100, word 328, word 122, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 391)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 392 := rfl

private theorem nodeClosure_eq_392 : nodeClosure 392 = smallEvenDescentNode 393 := by
  have hi : nodeGeneratorIndex 392 = ![92, 258, 120, 3, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 392 = Subgroup.closure ({word 92, word 258, word 120, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 392)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 5 * root 6 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 393 := rfl

private theorem nodeClosure_eq_393 : nodeClosure 393 = smallEvenDescentNode 394 := by
  have hi : nodeGeneratorIndex 393 = ![59, 112, 124, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 393 = Subgroup.closure ({word 59, word 112, word 124, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 393)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, root 2 * root 3 * root 4, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 394 := rfl

private theorem nodeClosure_eq_394 : nodeClosure 394 = smallEvenDescentNode 395 := by
  have hi : nodeGeneratorIndex 394 = ![76, 15, 21, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 394 = Subgroup.closure ({word 76, word 15, word 21, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 394)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 5 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 395 := rfl

private theorem nodeClosure_eq_395 : nodeClosure 395 = smallEvenDescentNode 396 := by
  have hi : nodeGeneratorIndex 395 = ![44, 34, 24, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 395 = Subgroup.closure ({word 44, word 34, word 24, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 395)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 396 := rfl

private theorem nodeClosure_eq_396 : nodeClosure 396 = smallEvenDescentNode 397 := by
  have hi : nodeGeneratorIndex 396 = ![44, 105, 124, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 396 = Subgroup.closure ({word 44, word 105, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 396)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 397 := rfl

private theorem nodeClosure_eq_397 : nodeClosure 397 = smallEvenDescentNode 398 := by
  have hi : nodeGeneratorIndex 397 = ![44, 110, 113, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 397 = Subgroup.closure ({word 44, word 110, word 113, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 397)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 2 * root 3 * root 5 * root 6 * root 9, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 398 := rfl

private theorem nodeClosure_eq_398 : nodeClosure 398 = smallEvenDescentNode 399 := by
  have hi : nodeGeneratorIndex 398 = ![92, 34, 124, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 398 = Subgroup.closure ({word 92, word 34, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 398)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 399 := rfl

private theorem nodeClosure_eq_399 : nodeClosure 399 = smallEvenDescentNode 400 := by
  have hi : nodeGeneratorIndex 399 = ![100, 34, 113, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 399 = Subgroup.closure ({word 100, word 34, word 113, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 399)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 400 := rfl

private theorem nodeClosure_eq_400 : nodeClosure 400 = smallEvenDescentNode 401 := by
  have hi : nodeGeneratorIndex 400 = ![92, 105, 124, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 400 = Subgroup.closure ({word 92, word 105, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 400)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 401 := rfl

private theorem nodeClosure_eq_401 : nodeClosure 401 = smallEvenDescentNode 402 := by
  have hi : nodeGeneratorIndex 401 = ![44, 34, 15, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 401 = Subgroup.closure ({word 44, word 34, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 401)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 4 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 402 := rfl

private theorem nodeClosure_eq_402 : nodeClosure 402 = smallEvenDescentNode 403 := by
  have hi : nodeGeneratorIndex 402 = ![49, 34, 124, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 402 = Subgroup.closure ({word 49, word 34, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 402)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 403 := rfl

private theorem nodeClosure_eq_403 : nodeClosure 403 = smallEvenDescentNode 404 := by
  have hi : nodeGeneratorIndex 403 = ![100, 34, 15, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 403 = Subgroup.closure ({word 100, word 34, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 403)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 4 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 404 := rfl

private theorem nodeClosure_eq_404 : nodeClosure 404 = smallEvenDescentNode 405 := by
  have hi : nodeGeneratorIndex 404 = ![49, 34, 113, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 404 = Subgroup.closure ({word 49, word 34, word 113, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 404)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 405 := rfl

private theorem nodeClosure_eq_405 : nodeClosure 405 = smallEvenDescentNode 406 := by
  have hi : nodeGeneratorIndex 405 = ![44, 43, 15, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 405 = Subgroup.closure ({word 44, word 43, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 405)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 406 := rfl

private theorem nodeClosure_eq_406 : nodeClosure 406 = smallEvenDescentNode 407 := by
  have hi : nodeGeneratorIndex 406 = ![44, 36, 21, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 406 = Subgroup.closure ({word 44, word 36, word 21, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 406)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 4 * root 6 * root 9, root 5 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 407 := rfl

private theorem nodeClosure_eq_407 : nodeClosure 407 = smallEvenDescentNode 408 := by
  have hi : nodeGeneratorIndex 407 = ![49, 105, 121, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 407 = Subgroup.closure ({word 49, word 105, word 121, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 407)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 408 := rfl

private theorem nodeClosure_eq_408 : nodeClosure 408 = smallEvenDescentNode 409 := by
  have hi : nodeGeneratorIndex 408 = ![100, 43, 15, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 408 = Subgroup.closure ({word 100, word 43, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 408)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 409 := rfl

private theorem nodeClosure_eq_409 : nodeClosure 409 = smallEvenDescentNode 410 := by
  have hi : nodeGeneratorIndex 409 = ![182, 15, 17, 4, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 409 = Subgroup.closure ({word 182, word 15, word 17, word 4, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 409)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 5 * root 6 * root 9, root 6 * root 7 * root 8 * root 9, root 5 * root 9, root 7, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 410 := rfl

private theorem nodeClosure_eq_410 : nodeClosure 410 = smallEvenDescentNode 411 := by
  have hi : nodeGeneratorIndex 410 = ![59, 330, 124, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 410 = Subgroup.closure ({word 59, word 330, word 124, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 410)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 411 := rfl

private theorem nodeClosure_eq_411 : nodeClosure 411 = smallEvenDescentNode 412 := by
  have hi : nodeGeneratorIndex 411 = ![59, 338, 119, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 411 = Subgroup.closure ({word 59, word 338, word 119, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 411)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 412 := rfl

private theorem nodeClosure_eq_412 : nodeClosure 412 = smallEvenDescentNode 413 := by
  have hi : nodeGeneratorIndex 412 = ![59, 254, 124, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 412 = Subgroup.closure ({word 59, word 254, word 124, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 412)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 413 := rfl

private theorem nodeClosure_eq_413 : nodeClosure 413 = smallEvenDescentNode 414 := by
  have hi : nodeGeneratorIndex 413 = ![59, 254, 119, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 413 = Subgroup.closure ({word 59, word 254, word 119, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 413)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 414 := rfl

private theorem nodeClosure_eq_414 : nodeClosure 414 = smallEvenDescentNode 415 := by
  have hi : nodeGeneratorIndex 414 = ![59, 327, 124, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 414 = Subgroup.closure ({word 59, word 327, word 124, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 414)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 2 * root 3 * root 4, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 415 := rfl

private theorem nodeClosure_eq_415 : nodeClosure 415 = smallEvenDescentNode 416 := by
  have hi : nodeGeneratorIndex 415 = ![59, 333, 119, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 415 = Subgroup.closure ({word 59, word 333, word 119, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 415)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 416 := rfl

private theorem nodeClosure_eq_416 : nodeClosure 416 = smallEvenDescentNode 417 := by
  have hi : nodeGeneratorIndex 416 = ![61, 250, 124, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 416 = Subgroup.closure ({word 61, word 250, word 124, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 416)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 6 * root 9, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 417 := rfl

private theorem nodeClosure_eq_417 : nodeClosure 417 = smallEvenDescentNode 418 := by
  have hi : nodeGeneratorIndex 417 = ![61, 250, 119, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 417 = Subgroup.closure ({word 61, word 250, word 119, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 417)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 6 * root 9, rootOne ^ 2, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 418 := rfl

private theorem nodeClosure_eq_418 : nodeClosure 418 = smallEvenDescentNode 419 := by
  have hi : nodeGeneratorIndex 418 = ![61, 330, 124, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 418 = Subgroup.closure ({word 61, word 330, word 124, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 418)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 6 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 419 := rfl

private theorem nodeClosure_eq_419 : nodeClosure 419 = smallEvenDescentNode 420 := by
  have hi : nodeGeneratorIndex 419 = ![61, 338, 119, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 419 = Subgroup.closure ({word 61, word 338, word 119, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 419)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 6 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 420 := rfl

private theorem nodeClosure_eq_420 : nodeClosure 420 = smallEvenDescentNode 421 := by
  have hi : nodeGeneratorIndex 420 = ![71, 250, 21, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 420 = Subgroup.closure ({word 71, word 250, word 21, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 420)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 8, rootOne ^ 2, root 5 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 421 := rfl

private theorem nodeClosure_eq_421 : nodeClosure 421 = smallEvenDescentNode 422 := by
  have hi : nodeGeneratorIndex 421 = ![61, 254, 124, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 421 = Subgroup.closure ({word 61, word 254, word 124, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 421)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 6 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 422 := rfl

private theorem nodeClosure_eq_422 : nodeClosure 422 = smallEvenDescentNode 423 := by
  have hi : nodeGeneratorIndex 422 = ![61, 254, 119, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 422 = Subgroup.closure ({word 61, word 254, word 119, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 422)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 6 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 423 := rfl

private theorem nodeClosure_eq_423 : nodeClosure 423 = smallEvenDescentNode 424 := by
  have hi : nodeGeneratorIndex 423 = ![61, 327, 124, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 423 = Subgroup.closure ({word 61, word 327, word 124, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 423)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 6 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 424 := rfl

private theorem nodeClosure_eq_424 : nodeClosure 424 = smallEvenDescentNode 425 := by
  have hi : nodeGeneratorIndex 424 = ![61, 333, 119, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 424 = Subgroup.closure ({word 61, word 333, word 119, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 424)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 6 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 425 := rfl

private theorem nodeClosure_eq_425 : nodeClosure 425 = smallEvenDescentNode 426 := by
  have hi : nodeGeneratorIndex 425 = ![71, 254, 21, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 425 = Subgroup.closure ({word 71, word 254, word 21, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 425)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 5 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 426 := rfl

private theorem nodeClosure_eq_426 : nodeClosure 426 = smallEvenDescentNode 427 := by
  have hi : nodeGeneratorIndex 426 = ![59, 250, 122, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 426 = Subgroup.closure ({word 59, word 250, word 122, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 426)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 427 := rfl

private theorem nodeClosure_eq_427 : nodeClosure 427 = smallEvenDescentNode 428 := by
  have hi : nodeGeneratorIndex 427 = ![59, 338, 122, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 427 = Subgroup.closure ({word 59, word 338, word 122, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 427)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 428 := rfl

private theorem nodeClosure_eq_428 : nodeClosure 428 = smallEvenDescentNode 429 := by
  have hi : nodeGeneratorIndex 428 = ![89, 250, 122, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 428 = Subgroup.closure ({word 89, word 250, word 122, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 428)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 429 := rfl

private theorem nodeClosure_eq_429 : nodeClosure 429 = smallEvenDescentNode 430 := by
  have hi : nodeGeneratorIndex 429 = ![89, 338, 15, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 429 = Subgroup.closure ({word 89, word 338, word 15, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 429)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 430 := rfl

private theorem nodeClosure_eq_430 : nodeClosure 430 = smallEvenDescentNode 431 := by
  have hi : nodeGeneratorIndex 430 = ![89, 338, 122, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 430 = Subgroup.closure ({word 89, word 338, word 122, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 430)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 431 := rfl

private theorem nodeClosure_eq_431 : nodeClosure 431 = smallEvenDescentNode 432 := by
  have hi : nodeGeneratorIndex 431 = ![59, 250, 112, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 431 = Subgroup.closure ({word 59, word 250, word 112, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 431)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, rootOne ^ 2, root 2 * root 3 * root 4, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 432 := rfl

private theorem nodeClosure_eq_432 : nodeClosure 432 = smallEvenDescentNode 433 := by
  have hi : nodeGeneratorIndex 432 = ![59, 330, 112, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 432 = Subgroup.closure ({word 59, word 330, word 112, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 432)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 2 * root 3 * root 4, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 433 := rfl

private theorem nodeClosure_eq_433 : nodeClosure 433 = smallEvenDescentNode 434 := by
  have hi : nodeGeneratorIndex 433 = ![76, 250, 112, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 433 = Subgroup.closure ({word 76, word 250, word 112, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 433)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 6 * root 7, rootOne ^ 2, root 2 * root 3 * root 4, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 434 := rfl

private theorem nodeClosure_eq_434 : nodeClosure 434 = smallEvenDescentNode 435 := by
  have hi : nodeGeneratorIndex 434 = ![76, 330, 112, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 434 = Subgroup.closure ({word 76, word 330, word 112, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 434)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 6 * root 7, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 2 * root 3 * root 4, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 435 := rfl

private theorem nodeClosure_eq_435 : nodeClosure 435 = smallEvenDescentNode 436 := by
  have hi : nodeGeneratorIndex 435 = ![59, 338, 112, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 435 = Subgroup.closure ({word 59, word 338, word 112, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 435)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 436 := rfl

private theorem nodeClosure_eq_436 : nodeClosure 436 = smallEvenDescentNode 437 := by
  have hi : nodeGeneratorIndex 436 = ![89, 250, 112, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 436 = Subgroup.closure ({word 89, word 250, word 112, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 436)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 4, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 437 := rfl

private theorem nodeClosure_eq_437 : nodeClosure 437 = smallEvenDescentNode 438 := by
  have hi : nodeGeneratorIndex 437 = ![59, 330, 122, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 437 = Subgroup.closure ({word 59, word 330, word 122, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 437)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 438 := rfl

private theorem nodeClosure_eq_438 : nodeClosure 438 = smallEvenDescentNode 439 := by
  have hi : nodeGeneratorIndex 438 = ![76, 330, 122, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 438 = Subgroup.closure ({word 76, word 330, word 122, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 438)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 6 * root 7, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 439 := rfl

private theorem nodeClosure_eq_439 : nodeClosure 439 = smallEvenDescentNode 440 := by
  have hi : nodeGeneratorIndex 439 = ![59, 255, 112, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 439 = Subgroup.closure ({word 59, word 255, word 112, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 439)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 5 * root 7 * root 8, root 2 * root 3 * root 4, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 440 := rfl

private theorem nodeClosure_eq_440 : nodeClosure 440 = smallEvenDescentNode 441 := by
  have hi : nodeGeneratorIndex 440 = ![59, 255, 123, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 440 = Subgroup.closure ({word 59, word 255, word 123, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 440)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 5 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 441 := rfl

private theorem nodeClosure_eq_441 : nodeClosure 441 = smallEvenDescentNode 442 := by
  have hi : nodeGeneratorIndex 441 = ![89, 330, 15, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 441 = Subgroup.closure ({word 89, word 330, word 15, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 441)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 442 := rfl

private theorem nodeClosure_eq_442 : nodeClosure 442 = smallEvenDescentNode 443 := by
  have hi : nodeGeneratorIndex 442 = ![89, 330, 122, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 442 = Subgroup.closure ({word 89, word 330, word 122, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 442)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 443 := rfl

private theorem nodeClosure_eq_443 : nodeClosure 443 = smallEvenDescentNode 444 := by
  have hi : nodeGeneratorIndex 443 = ![76, 255, 112, 6, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 443 = Subgroup.closure ({word 76, word 255, word 112, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 443)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 6 * root 7, rootOne ^ 2 * root 5 * root 7 * root 8, root 2 * root 3 * root 4, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 444 := rfl

private theorem nodeClosure_eq_444 : nodeClosure 444 = smallEvenDescentNode 445 := by
  have hi : nodeGeneratorIndex 444 = ![157, 182, 13, 4, 16, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 444 = Subgroup.closure ({word 157, word 182, word 13, word 4, word 16, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 444)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0, root 0 * root 2 * root 5 * root 6 * root 9, root 6 * root 7 * root 9, root 7, root 5, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 445 := rfl

private theorem nodeClosure_eq_445 : nodeClosure 445 = smallEvenDescentNode 446 := by
  have hi : nodeGeneratorIndex 445 = ![158, 182, 13, 4, 16, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 445 = Subgroup.closure ({word 158, word 182, word 13, word 4, word 16, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 445)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 8, root 0 * root 2 * root 5 * root 6 * root 9, root 6 * root 7 * root 9, root 7, root 5, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 446 := rfl

private theorem nodeClosure_eq_446 : nodeClosure 446 = smallEvenDescentNode 447 := by
  have hi : nodeGeneratorIndex 446 = ![266, 34, 124, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 446 = Subgroup.closure ({word 266, word 34, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 446)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 447 := rfl

private theorem nodeClosure_eq_447 : nodeClosure 447 = smallEvenDescentNode 448 := by
  have hi : nodeGeneratorIndex 447 = ![266, 105, 124, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 447 = Subgroup.closure ({word 266, word 105, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 447)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 448 := rfl

private theorem nodeClosure_eq_448 : nodeClosure 448 = smallEvenDescentNode 449 := by
  have hi : nodeGeneratorIndex 448 = ![266, 110, 113, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 448 = Subgroup.closure ({word 266, word 110, word 113, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 448)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3, root 2 * root 3 * root 5 * root 6 * root 9, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 449 := rfl

private theorem nodeClosure_eq_449 : nodeClosure 449 = smallEvenDescentNode 450 := by
  have hi : nodeGeneratorIndex 449 = ![302, 34, 124, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 449 = Subgroup.closure ({word 302, word 34, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 449)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 2 * root 4 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 450 := rfl

private theorem nodeClosure_eq_450 : nodeClosure 450 = smallEvenDescentNode 451 := by
  have hi : nodeGeneratorIndex 450 = ![312, 34, 113, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 450 = Subgroup.closure ({word 312, word 34, word 113, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 450)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 451 := rfl

private theorem nodeClosure_eq_451 : nodeClosure 451 = smallEvenDescentNode 452 := by
  have hi : nodeGeneratorIndex 451 = ![302, 34, 24, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 451 = Subgroup.closure ({word 302, word 34, word 24, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 451)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 2 * root 4 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 452 := rfl

private theorem nodeClosure_eq_452 : nodeClosure 452 = smallEvenDescentNode 453 := by
  have hi : nodeGeneratorIndex 452 = ![312, 110, 113, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 452 = Subgroup.closure ({word 312, word 110, word 113, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 452)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 2 * root 3 * root 5 * root 6 * root 9, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 453 := rfl

private theorem nodeClosure_eq_453 : nodeClosure 453 = smallEvenDescentNode 454 := by
  have hi : nodeGeneratorIndex 453 = ![266, 34, 15, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 453 = Subgroup.closure ({word 266, word 34, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 453)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3, root 4 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 454 := rfl

private theorem nodeClosure_eq_454 : nodeClosure 454 = smallEvenDescentNode 455 := by
  have hi : nodeGeneratorIndex 454 = ![275, 34, 124, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 454 = Subgroup.closure ({word 275, word 34, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 454)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 455 := rfl

private theorem nodeClosure_eq_455 : nodeClosure 455 = smallEvenDescentNode 456 := by
  have hi : nodeGeneratorIndex 455 = ![312, 34, 15, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 455 = Subgroup.closure ({word 312, word 34, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 455)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 4 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 456 := rfl

private theorem nodeClosure_eq_456 : nodeClosure 456 = smallEvenDescentNode 457 := by
  have hi : nodeGeneratorIndex 456 = ![266, 36, 119, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 456 = Subgroup.closure ({word 266, word 36, word 119, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 456)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3, root 4 * root 6 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 457 := rfl

private theorem nodeClosure_eq_457 : nodeClosure 457 = smallEvenDescentNode 458 := by
  have hi : nodeGeneratorIndex 457 = ![266, 43, 15, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 457 = Subgroup.closure ({word 266, word 43, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 457)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 458 := rfl

private theorem nodeClosure_eq_458 : nodeClosure 458 = smallEvenDescentNode 459 := by
  have hi : nodeGeneratorIndex 458 = ![275, 34, 24, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 458 = Subgroup.closure ({word 275, word 34, word 24, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 458)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 459 := rfl

private theorem nodeClosure_eq_459 : nodeClosure 459 = smallEvenDescentNode 460 := by
  have hi : nodeGeneratorIndex 459 = ![275, 106, 124, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 459 = Subgroup.closure ({word 275, word 106, word 124, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 459)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 6 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 460 := rfl

private theorem nodeClosure_eq_460 : nodeClosure 460 = smallEvenDescentNode 461 := by
  have hi : nodeGeneratorIndex 460 = ![167, 194, 5, 19, 13, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 460 = Subgroup.closure ({word 167, word 194, word 5, word 19, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 460)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 7 * root 9, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 461 := rfl

private theorem nodeClosure_eq_461 : nodeClosure 461 = smallEvenDescentNode 462 := by
  have hi : nodeGeneratorIndex 461 = ![44, 250, 34, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 461 = Subgroup.closure ({word 44, word 250, word 34, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 461)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 462 := rfl

private theorem nodeClosure_eq_462 : nodeClosure 462 = smallEvenDescentNode 463 := by
  have hi : nodeGeneratorIndex 462 = ![100, 338, 34, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 462 = Subgroup.closure ({word 100, word 338, word 34, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 462)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 463 := rfl

private theorem nodeClosure_eq_463 : nodeClosure 463 = smallEvenDescentNode 464 := by
  have hi : nodeGeneratorIndex 463 = ![92, 250, 34, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 463 = Subgroup.closure ({word 92, word 250, word 34, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 463)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 464 := rfl

private theorem nodeClosure_eq_464 : nodeClosure 464 = smallEvenDescentNode 465 := by
  have hi : nodeGeneratorIndex 464 = ![44, 258, 34, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 464 = Subgroup.closure ({word 44, word 258, word 34, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 464)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 5 * root 6 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 465 := rfl

private theorem nodeClosure_eq_465 : nodeClosure 465 = smallEvenDescentNode 466 := by
  have hi : nodeGeneratorIndex 465 = ![54, 250, 43, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 465 = Subgroup.closure ({word 54, word 250, word 43, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 465)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 5 * root 6 * root 9, rootOne ^ 2, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 466 := rfl

private theorem nodeClosure_eq_466 : nodeClosure 466 = smallEvenDescentNode 467 := by
  have hi : nodeGeneratorIndex 466 = ![44, 338, 43, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 466 = Subgroup.closure ({word 44, word 338, word 43, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 466)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 467 := rfl

private theorem nodeClosure_eq_467 : nodeClosure 467 = smallEvenDescentNode 468 := by
  have hi : nodeGeneratorIndex 467 = ![100, 250, 43, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 467 = Subgroup.closure ({word 100, word 250, word 43, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 467)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 468 := rfl

private theorem nodeClosure_eq_468 : nodeClosure 468 = smallEvenDescentNode 469 := by
  have hi : nodeGeneratorIndex 468 = ![100, 338, 43, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 468 = Subgroup.closure ({word 100, word 338, word 43, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 468)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 469 := rfl

private theorem nodeClosure_eq_469 : nodeClosure 469 = smallEvenDescentNode 470 := by
  have hi : nodeGeneratorIndex 469 = ![44, 328, 43, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 469 = Subgroup.closure ({word 44, word 328, word 43, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 469)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 470 := rfl

private theorem nodeClosure_eq_470 : nodeClosure 470 = smallEvenDescentNode 471 := by
  have hi : nodeGeneratorIndex 470 = ![92, 328, 43, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 470 = Subgroup.closure ({word 92, word 328, word 43, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 470)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 471 := rfl

private theorem nodeClosure_eq_471 : nodeClosure 471 = smallEvenDescentNode 472 := by
  have hi : nodeGeneratorIndex 471 = ![100, 328, 34, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 471 = Subgroup.closure ({word 100, word 328, word 34, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 471)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 472 := rfl

private theorem nodeClosure_eq_472 : nodeClosure 472 = smallEvenDescentNode 473 := by
  have hi : nodeGeneratorIndex 472 = ![100, 258, 34, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 472 = Subgroup.closure ({word 100, word 258, word 34, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 472)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 5 * root 6 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 473 := rfl

private theorem nodeClosure_eq_473 : nodeClosure 473 = smallEvenDescentNode 474 := by
  have hi : nodeGeneratorIndex 473 = ![92, 338, 34, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 473 = Subgroup.closure ({word 92, word 338, word 34, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 473)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 474 := rfl

private theorem nodeClosure_eq_474 : nodeClosure 474 = smallEvenDescentNode 475 := by
  have hi : nodeGeneratorIndex 474 = ![92, 258, 34, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 474 = Subgroup.closure ({word 92, word 258, word 34, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 474)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 5 * root 6 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 475 := rfl

private theorem nodeClosure_eq_475 : nodeClosure 475 = smallEvenDescentNode 476 := by
  have hi : nodeGeneratorIndex 475 = ![54, 328, 34, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 475 = Subgroup.closure ({word 54, word 328, word 34, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 475)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 5 * root 6 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 476 := rfl

private theorem nodeClosure_eq_476 : nodeClosure 476 = smallEvenDescentNode 477 := by
  have hi : nodeGeneratorIndex 476 = ![54, 328, 43, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 476 = Subgroup.closure ({word 54, word 328, word 43, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 476)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 5 * root 6 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 477 := rfl

private theorem nodeClosure_eq_477 : nodeClosure 477 = smallEvenDescentNode 478 := by
  have hi : nodeGeneratorIndex 477 = ![100, 328, 43, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 477 = Subgroup.closure ({word 100, word 328, word 43, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 477)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 478 := rfl

private theorem nodeClosure_eq_478 : nodeClosure 478 = smallEvenDescentNode 479 := by
  have hi : nodeGeneratorIndex 478 = ![100, 258, 43, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 478 = Subgroup.closure ({word 100, word 258, word 43, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 478)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 5 * root 6 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 479 := rfl

private theorem nodeClosure_eq_479 : nodeClosure 479 = smallEvenDescentNode 480 := by
  have hi : nodeGeneratorIndex 479 = ![92, 258, 43, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 479 = Subgroup.closure ({word 92, word 258, word 43, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 479)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 5 * root 6 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 480 := rfl

private theorem nodeClosure_eq_480 : nodeClosure 480 = smallEvenDescentNode 481 := by
  have hi : nodeGeneratorIndex 480 = ![44, 254, 34, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 480 = Subgroup.closure ({word 44, word 254, word 34, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 480)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 481 := rfl

private theorem nodeClosure_eq_481 : nodeClosure 481 = smallEvenDescentNode 482 := by
  have hi : nodeGeneratorIndex 481 = ![49, 250, 34, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 481 = Subgroup.closure ({word 49, word 250, word 34, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 481)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 482 := rfl

private theorem nodeClosure_eq_482 : nodeClosure 482 = smallEvenDescentNode 483 := by
  have hi : nodeGeneratorIndex 482 = ![49, 254, 34, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 482 = Subgroup.closure ({word 49, word 254, word 34, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 482)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 483 := rfl

private theorem nodeClosure_eq_483 : nodeClosure 483 = smallEvenDescentNode 484 := by
  have hi : nodeGeneratorIndex 483 = ![44, 332, 36, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 483 = Subgroup.closure ({word 44, word 332, word 36, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 483)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 8, root 4 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 484 := rfl

private theorem nodeClosure_eq_484 : nodeClosure 484 = smallEvenDescentNode 485 := by
  have hi : nodeGeneratorIndex 484 = ![97, 332, 36, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 484 = Subgroup.closure ({word 97, word 332, word 36, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 484)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 7, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 8, root 4 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 485 := rfl

private theorem nodeClosure_eq_485 : nodeClosure 485 = smallEvenDescentNode 486 := by
  have hi : nodeGeneratorIndex 485 = ![100, 254, 34, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 485 = Subgroup.closure ({word 100, word 254, word 34, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 485)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 486 := rfl

private theorem nodeClosure_eq_486 : nodeClosure 486 = smallEvenDescentNode 487 := by
  have hi : nodeGeneratorIndex 486 = ![100, 333, 34, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 486 = Subgroup.closure ({word 100, word 333, word 34, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 486)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 487 := rfl

private theorem nodeClosure_eq_487 : nodeClosure 487 = smallEvenDescentNode 488 := by
  have hi : nodeGeneratorIndex 487 = ![49, 338, 34, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 487 = Subgroup.closure ({word 49, word 338, word 34, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 487)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 488 := rfl

private theorem nodeClosure_eq_488 : nodeClosure 488 = smallEvenDescentNode 489 := by
  have hi : nodeGeneratorIndex 488 = ![44, 330, 36, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 488 = Subgroup.closure ({word 44, word 330, word 36, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 488)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 4 * root 6 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 489 := rfl

private theorem nodeClosure_eq_489 : nodeClosure 489 = smallEvenDescentNode 490 := by
  have hi : nodeGeneratorIndex 489 = ![92, 331, 34, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 489 = Subgroup.closure ({word 92, word 331, word 34, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 489)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 490 := rfl

private theorem nodeClosure_eq_490 : nodeClosure 490 = smallEvenDescentNode 491 := by
  have hi : nodeGeneratorIndex 490 = ![49, 328, 34, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 490 = Subgroup.closure ({word 49, word 328, word 34, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 490)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 491 := rfl

private theorem nodeClosure_eq_491 : nodeClosure 491 = smallEvenDescentNode 492 := by
  have hi : nodeGeneratorIndex 491 = ![44, 254, 43, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 491 = Subgroup.closure ({word 44, word 254, word 43, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 491)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 492 := rfl

private theorem nodeClosure_eq_492 : nodeClosure 492 = smallEvenDescentNode 493 := by
  have hi : nodeGeneratorIndex 492 = ![49, 250, 38, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 492 = Subgroup.closure ({word 49, word 250, word 38, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 492)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 5, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 493 := rfl

private theorem nodeClosure_eq_493 : nodeClosure 493 = smallEvenDescentNode 494 := by
  have hi : nodeGeneratorIndex 493 = ![49, 254, 38, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 493 = Subgroup.closure ({word 49, word 254, word 38, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 493)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 4 * root 5, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 494 := rfl

private theorem nodeClosure_eq_494 : nodeClosure 494 = smallEvenDescentNode 495 := by
  have hi : nodeGeneratorIndex 494 = ![49, 258, 34, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 494 = Subgroup.closure ({word 49, word 258, word 34, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 494)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 5 * root 6 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 495 := rfl

private theorem nodeClosure_eq_495 : nodeClosure 495 = smallEvenDescentNode 496 := by
  have hi : nodeGeneratorIndex 495 = ![100, 333, 43, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 495 = Subgroup.closure ({word 100, word 333, word 43, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 495)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 496 := rfl

private theorem nodeClosure_eq_496 : nodeClosure 496 = smallEvenDescentNode 497 := by
  have hi : nodeGeneratorIndex 496 = ![100, 254, 39, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 496 = Subgroup.closure ({word 100, word 254, word 39, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 496)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 4 * root 5 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 497 := rfl

private theorem nodeClosure_eq_497 : nodeClosure 497 = smallEvenDescentNode 498 := by
  have hi : nodeGeneratorIndex 497 = ![131, 2, 17, 15, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 497 = Subgroup.closure ({word 131, word 2, word 17, word 15, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 497)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 1 * root 5 * root 6 * root 7 * root 8 * root 9, root 8, root 5 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 498 := rfl

private theorem nodeClosure_eq_498 : nodeClosure 498 = smallEvenDescentNode 499 := by
  have hi : nodeGeneratorIndex 498 = ![44, 141, 10, 18, 2, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 498 = Subgroup.closure ({word 44, word 141, word 10, word 18, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 498)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 6 * root 8, root 5 * root 8, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 499 := rfl

private theorem nodeClosure_eq_499 : nodeClosure 499 = smallEvenDescentNode 500 := by
  have hi : nodeGeneratorIndex 499 = ![44, 141, 4, 18, 2, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 499 = Subgroup.closure ({word 44, word 141, word 4, word 18, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 499)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 7, root 5 * root 8, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 500 := rfl

private theorem nodeClosure_eq_500 : nodeClosure 500 = smallEvenDescentNode 501 := by
  have hi : nodeGeneratorIndex 500 = ![44, 141, 14, 18, 2, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 500 = Subgroup.closure ({word 44, word 141, word 14, word 18, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 500)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 6 * root 7 * root 8, root 5 * root 8, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 501 := rfl

private theorem nodeClosure_eq_501 : nodeClosure 501 = smallEvenDescentNode 502 := by
  have hi : nodeGeneratorIndex 501 = ![73, 141, 2, 18, 12, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 501 = Subgroup.closure ({word 73, word 141, word 2, word 18, word 12, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 501)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 7, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 8, root 5 * root 8, root 6 * root 7, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 502 := rfl

private theorem nodeClosure_eq_502 : nodeClosure 502 = smallEvenDescentNode 503 := by
  have hi : nodeGeneratorIndex 502 = ![340, 38, 15, 5, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 502 = Subgroup.closure ({word 340, word 38, word 15, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 502)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 1 * root 5 * root 6 * root 7 * root 8 * root 9, root 4 * root 5, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 503 := rfl

private theorem nodeClosure_eq_503 : nodeClosure 503 = smallEvenDescentNode 504 := by
  have hi : nodeGeneratorIndex 503 = ![44, 348, 10, 40, 2, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 503 = Subgroup.closure ({word 44, word 348, word 10, word 40, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 503)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 6 * root 8, root 4 * root 5 * root 8 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 504 := rfl

private theorem nodeClosure_eq_504 : nodeClosure 504 = smallEvenDescentNode 505 := by
  have hi : nodeGeneratorIndex 504 = ![44, 348, 4, 40, 2, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 504 = Subgroup.closure ({word 44, word 348, word 4, word 40, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 504)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 7, root 4 * root 5 * root 8 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 505 := rfl

private theorem nodeClosure_eq_505 : nodeClosure 505 = smallEvenDescentNode 506 := by
  have hi : nodeGeneratorIndex 505 = ![46, 348, 4, 40, 2, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 505 = Subgroup.closure ({word 46, word 348, word 4, word 40, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 505)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 8, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 7, root 4 * root 5 * root 8 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 506 := rfl

private theorem nodeClosure_eq_506 : nodeClosure 506 = smallEvenDescentNode 507 := by
  have hi : nodeGeneratorIndex 506 = ![90, 348, 40, 11, 3, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 506 = Subgroup.closure ({word 90, word 348, word 40, word 11, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 506)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 5 * root 8 * root 9, root 6 * root 8 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 507 := rfl

private theorem nodeClosure_eq_507 : nodeClosure 507 = smallEvenDescentNode 508 := by
  have hi : nodeGeneratorIndex 507 = ![200, 235, 2, 8, 22, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 507 = Subgroup.closure ({word 200, word 235, word 2, word 8, word 22, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 507)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 8, root 6, root 5 * root 7 * root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 508 := rfl

private theorem nodeClosure_eq_508 : nodeClosure 508 = smallEvenDescentNode 509 := by
  have hi : nodeGeneratorIndex 508 = ![200, 235, 10, 5, 22, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 508 = Subgroup.closure ({word 200, word 235, word 10, word 5, word 22, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 508)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 6 * root 8, root 7 * root 9, root 5 * root 7 * root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 509 := rfl

private theorem nodeClosure_eq_509 : nodeClosure 509 = smallEvenDescentNode 510 := by
  have hi : nodeGeneratorIndex 509 = ![200, 235, 7, 13, 22, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 509 = Subgroup.closure ({word 200, word 235, word 7, word 13, word 22, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 509)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 7 * root 8 * root 9, root 6 * root 7 * root 9, root 5 * root 7 * root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 510 := rfl

private theorem nodeClosure_eq_510 : nodeClosure 510 = smallEvenDescentNode 511 := by
  have hi : nodeGeneratorIndex 510 = ![200, 239, 2, 8, 22, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 510 = Subgroup.closure ({word 200, word 239, word 2, word 8, word 22, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 510)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 1 * root 2 * root 3 * root 6 * root 7 * root 8 * root 9, root 8, root 6, root 5 * root 7 * root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 511 := rfl

private theorem nodeClosure_eq_511 : nodeClosure 511 = smallEvenDescentNode 512 := by
  have hi : nodeGeneratorIndex 511 = ![200, 239, 7, 13, 22, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 511 = Subgroup.closure ({word 200, word 239, word 7, word 13, word 22, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 511)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 1 * root 2 * root 3 * root 6 * root 7 * root 8 * root 9, root 7 * root 8 * root 9, root 6 * root 7 * root 9, root 5 * root 7 * root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 512 := rfl

private theorem nodeClosure_eq_512 : nodeClosure 512 = smallEvenDescentNode 513 := by
  have hi : nodeGeneratorIndex 512 = ![202, 235, 10, 5, 22, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 512 = Subgroup.closure ({word 202, word 235, word 10, word 5, word 22, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 512)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 3 * root 4 * root 6 * root 7, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 6 * root 8, root 7 * root 9, root 5 * root 7 * root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 513 := rfl

private theorem nodeClosure_eq_513 : nodeClosure 513 = smallEvenDescentNode 514 := by
  have hi : nodeGeneratorIndex 513 = ![167, 235, 22, 8, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 513 = Subgroup.closure ({word 167, word 235, word 22, word 8, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 513)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 514 := rfl

private theorem nodeClosure_eq_514 : nodeClosure 514 = smallEvenDescentNode 515 := by
  have hi : nodeGeneratorIndex 514 = ![167, 246, 22, 8, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 514 = Subgroup.closure ({word 167, word 246, word 22, word 8, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 514)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 7, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 515 := rfl

private theorem nodeClosure_eq_515 : nodeClosure 515 = smallEvenDescentNode 516 := by
  have hi : nodeGeneratorIndex 515 = ![167, 248, 22, 8, 5, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 515 = Subgroup.closure ({word 167, word 248, word 22, word 8, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 515)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 516 := rfl

private theorem nodeClosure_eq_516 : nodeClosure 516 = smallEvenDescentNode 517 := by
  have hi : nodeGeneratorIndex 516 = ![167, 235, 2, 22, 13, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 516 = Subgroup.closure ({word 167, word 235, word 2, word 22, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 516)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 8, root 5 * root 7 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 517 := rfl

private theorem nodeClosure_eq_517 : nodeClosure 517 = smallEvenDescentNode 518 := by
  have hi : nodeGeneratorIndex 517 = ![167, 235, 7, 22, 13, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 517 = Subgroup.closure ({word 167, word 235, word 7, word 22, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 517)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 7 * root 8 * root 9, root 5 * root 7 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 518 := rfl

private theorem nodeClosure_eq_518 : nodeClosure 518 = smallEvenDescentNode 519 := by
  have hi : nodeGeneratorIndex 518 = ![167, 246, 2, 29, 13, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 518 = Subgroup.closure ({word 167, word 246, word 2, word 29, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 518)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 7, root 8, root 5 * root 6 * root 7 * root 8, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 519 := rfl

private theorem nodeClosure_eq_519 : nodeClosure 519 = smallEvenDescentNode 520 := by
  have hi : nodeGeneratorIndex 519 = ![167, 246, 7, 29, 13, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 519 = Subgroup.closure ({word 167, word 246, word 7, word 29, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 519)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 7, root 7 * root 8 * root 9, root 5 * root 6 * root 7 * root 8, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 520 := rfl

private theorem nodeClosure_eq_520 : nodeClosure 520 = smallEvenDescentNode 521 := by
  have hi : nodeGeneratorIndex 520 = ![164, 246, 7, 29, 13, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 520 = Subgroup.closure ({word 164, word 246, word 7, word 29, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 520)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 8 * root 9, root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 7, root 7 * root 8 * root 9, root 5 * root 6 * root 7 * root 8, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 521 := rfl

private theorem nodeClosure_eq_521 : nodeClosure 521 = smallEvenDescentNode 522 := by
  have hi : nodeGeneratorIndex 521 = ![194, 141, 6, 30, 12, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 521 = Subgroup.closure ({word 194, word 141, word 6, word 30, word 12, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 521)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 522 := rfl

private theorem nodeClosure_eq_522 : nodeClosure 522 = smallEvenDescentNode 523 := by
  have hi : nodeGeneratorIndex 522 = ![194, 141, 3, 30, 12, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 522 = Subgroup.closure ({word 194, word 141, word 3, word 30, word 12, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 522)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 523 := rfl

private theorem nodeClosure_eq_523 : nodeClosure 523 = smallEvenDescentNode 524 := by
  have hi : nodeGeneratorIndex 523 = ![194, 141, 5, 30, 12, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 523 = Subgroup.closure ({word 194, word 141, word 5, word 30, word 12, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 523)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 524 := rfl

private theorem nodeClosure_eq_524 : nodeClosure 524 = smallEvenDescentNode 525 := by
  have hi : nodeGeneratorIndex 524 = ![194, 142, 6, 30, 12, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 524 = Subgroup.closure ({word 194, word 142, word 6, word 30, word 12, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 524)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 8, root 7 * root 8, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 525 := rfl

private theorem nodeClosure_eq_525 : nodeClosure 525 = smallEvenDescentNode 526 := by
  have hi : nodeGeneratorIndex 525 = ![190, 141, 3, 30, 12, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 525 = Subgroup.closure ({word 190, word 141, word 3, word 30, word 12, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 525)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 4 * root 5 * root 6, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 526 := rfl

private theorem nodeClosure_eq_526 : nodeClosure 526 = smallEvenDescentNode 527 := by
  have hi : nodeGeneratorIndex 526 = ![167, 194, 141, 19, 13, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 526 = Subgroup.closure ({word 167, word 194, word 141, word 19, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 526)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 527 := rfl

private theorem nodeClosure_eq_527 : nodeClosure 527 = smallEvenDescentNode 528 := by
  have hi : nodeGeneratorIndex 527 = ![167, 194, 138, 19, 13, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 527 = Subgroup.closure ({word 167, word 194, word 138, word 19, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 527)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 528 := rfl

private theorem nodeClosure_eq_528 : nodeClosure 528 = smallEvenDescentNode 529 := by
  have hi : nodeGeneratorIndex 528 = ![167, 191, 141, 19, 13, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 528 = Subgroup.closure ({word 167, word 191, word 141, word 19, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 528)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 529 := rfl

private theorem nodeClosure_eq_529 : nodeClosure 529 = smallEvenDescentNode 530 := by
  have hi : nodeGeneratorIndex 529 = ![167, 191, 138, 19, 13, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 529 = Subgroup.closure ({word 167, word 191, word 138, word 19, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 529)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 1 * root 3 * root 5 * root 6, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 530 := rfl

private theorem nodeClosure_eq_530 : nodeClosure 530 = smallEvenDescentNode 531 := by
  have hi : nodeGeneratorIndex 530 = ![164, 194, 141, 19, 13, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 530 = Subgroup.closure ({word 164, word 194, word 141, word 19, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 530)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 8 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 531 := rfl

private theorem nodeClosure_eq_531 : nodeClosure 531 = smallEvenDescentNode 532 := by
  have hi : nodeGeneratorIndex 531 = ![164, 194, 138, 19, 13, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 531 = Subgroup.closure ({word 164, word 194, word 138, word 19, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 531)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 8 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 532 := rfl

private theorem nodeClosure_eq_532 : nodeClosure 532 = smallEvenDescentNode 533 := by
  have hi : nodeGeneratorIndex 532 = ![164, 191, 141, 19, 13, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 532 = Subgroup.closure ({word 164, word 191, word 141, word 19, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 532)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 8 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 533 := rfl

private theorem nodeClosure_eq_533 : nodeClosure 533 = smallEvenDescentNode 534 := by
  have hi : nodeGeneratorIndex 533 = ![164, 191, 138, 19, 13, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 533 = Subgroup.closure ({word 164, word 191, word 138, word 19, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 533)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 8 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 1 * root 3 * root 5 * root 6, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 534 := rfl

private theorem nodeClosure_eq_534 : nodeClosure 534 = smallEvenDescentNode 535 := by
  have hi : nodeGeneratorIndex 534 = ![167, 194, 142, 19, 13, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 534 = Subgroup.closure ({word 167, word 194, word 142, word 19, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 534)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 8, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 535 := rfl

private theorem nodeClosure_eq_535 : nodeClosure 535 = smallEvenDescentNode 536 := by
  have hi : nodeGeneratorIndex 535 = ![167, 193, 141, 19, 13, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 535 = Subgroup.closure ({word 167, word 193, word 141, word 19, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 535)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 536 := rfl

private theorem nodeClosure_eq_536 : nodeClosure 536 = smallEvenDescentNode 537 := by
  have hi : nodeGeneratorIndex 536 = ![166, 194, 141, 19, 13, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 536 = Subgroup.closure ({word 166, word 194, word 141, word 19, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 536)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 537 := rfl

private theorem nodeClosure_eq_537 : nodeClosure 537 = smallEvenDescentNode 538 := by
  have hi : nodeGeneratorIndex 537 = ![166, 193, 142, 19, 13, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 537 = Subgroup.closure ({word 166, word 193, word 142, word 19, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 537)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 8, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 538 := rfl

private theorem nodeClosure_eq_538 : nodeClosure 538 = smallEvenDescentNode 539 := by
  have hi : nodeGeneratorIndex 538 = ![167, 190, 141, 19, 13, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 538 = Subgroup.closure ({word 167, word 190, word 141, word 19, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 538)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 539 := rfl

private theorem nodeClosure_eq_539 : nodeClosure 539 = smallEvenDescentNode 540 := by
  have hi : nodeGeneratorIndex 539 = ![167, 191, 142, 19, 13, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 539 = Subgroup.closure ({word 167, word 191, word 142, word 19, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 539)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 8, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 540 := rfl

private theorem nodeClosure_eq_540 : nodeClosure 540 = smallEvenDescentNode 541 := by
  have hi : nodeGeneratorIndex 540 = ![164, 191, 142, 19, 13, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 540 = Subgroup.closure ({word 164, word 191, word 142, word 19, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 540)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 8 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 8, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 541 := rfl

private theorem nodeClosure_eq_541 : nodeClosure 541 = smallEvenDescentNode 542 := by
  have hi : nodeGeneratorIndex 541 = ![164, 191, 140, 19, 13, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 541 = Subgroup.closure ({word 164, word 191, word 140, word 19, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 541)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 8 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 1 * root 3 * root 5 * root 6 * root 8 * root 9, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 542 := rfl

private theorem nodeClosure_eq_542 : nodeClosure 542 = smallEvenDescentNode 543 := by
  have hi : nodeGeneratorIndex 542 = ![355, 124, 114, 1, 5, 5, 5, 5, 5, 5] := rfl
  calc
    nodeClosure 542 = Subgroup.closure ({word 355, word 124, word 114, word 1, word 5} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 542)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 8, root 9, root 7 * root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 543 := rfl

private theorem nodeClosure_eq_543 : nodeClosure 543 = smallEvenDescentNode 544 := by
  have hi : nodeGeneratorIndex 543 = ![355, 3, 114, 1, 5, 5, 5, 5, 5, 5] := rfl
  calc
    nodeClosure 543 = Subgroup.closure ({word 355, word 3, word 114, word 1, word 5} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 543)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 3, root 8 * root 9, root 2 * root 3 * root 4 * root 8, root 9, root 7 * root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 544 := rfl

private theorem nodeClosure_eq_544 : nodeClosure 544 = smallEvenDescentNode 545 := by
  have hi : nodeGeneratorIndex 544 = ![355, 125, 114, 1, 5, 5, 5, 5, 5, 5] := rfl
  calc
    nodeClosure 544 = Subgroup.closure ({word 355, word 125, word 114, word 1, word 5} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 544)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 8, root 9, root 7 * root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 545 := rfl

private theorem nodeClosure_eq_545 : nodeClosure 545 = smallEvenDescentNode 546 := by
  have hi : nodeGeneratorIndex 545 = ![194, 114, 30, 5, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 545 = Subgroup.closure ({word 194, word 114, word 30, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 545)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 8, root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 546 := rfl

private theorem nodeClosure_eq_546 : nodeClosure 546 = smallEvenDescentNode 547 := by
  have hi : nodeGeneratorIndex 546 = ![266, 124, 3, 5, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 546 = Subgroup.closure ({word 266, word 124, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 546)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 547 := rfl

private theorem nodeClosure_eq_547 : nodeClosure 547 = smallEvenDescentNode 548 := by
  have hi : nodeGeneratorIndex 547 = ![100, 338, 1, 2, 5, 5, 5, 5, 5, 5] := rfl
  calc
    nodeClosure 547 = Subgroup.closure ({word 100, word 338, word 1, word 2, word 5} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 547)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 9, root 8, root 7 * root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 548 := rfl

private theorem nodeClosure_eq_548 : nodeClosure 548 = smallEvenDescentNode 549 := by
  have hi : nodeGeneratorIndex 548 = ![100, 328, 3, 5, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 548 = Subgroup.closure ({word 100, word 328, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 548)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 549 := rfl

private theorem nodeClosure_eq_549 : nodeClosure 549 = smallEvenDescentNode 550 := by
  have hi : nodeGeneratorIndex 549 = ![49, 124, 3, 5, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 549 = Subgroup.closure ({word 49, word 124, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 549)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 550 := rfl

private theorem nodeClosure_eq_550 : nodeClosure 550 = smallEvenDescentNode 551 := by
  have hi : nodeGeneratorIndex 550 = ![49, 113, 3, 5, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 550 = Subgroup.closure ({word 49, word 113, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 550)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 551 := rfl

private theorem nodeClosure_eq_551 : nodeClosure 551 = smallEvenDescentNode 552 := by
  have hi : nodeGeneratorIndex 551 = ![100, 15, 3, 5, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 551 = Subgroup.closure ({word 100, word 15, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 551)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 552 := rfl

private theorem nodeClosure_eq_552 : nodeClosure 552 = smallEvenDescentNode 553 := by
  have hi : nodeGeneratorIndex 552 = ![44, 21, 5, 2, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 552 = Subgroup.closure ({word 44, word 21, word 5, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 552)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 5 * root 7 * root 8, root 7 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 553 := rfl

private theorem nodeClosure_eq_553 : nodeClosure 553 = smallEvenDescentNode 554 := by
  have hi : nodeGeneratorIndex 553 = ![275, 3, 124, 5, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 553 = Subgroup.closure ({word 275, word 3, word 124, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 553)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3 * root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 554 := rfl

private theorem nodeClosure_eq_554 : nodeClosure 554 = smallEvenDescentNode 555 := by
  have hi : nodeGeneratorIndex 554 = ![275, 3, 117, 5, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 554 = Subgroup.closure ({word 275, word 3, word 117, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 554)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3 * root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 2 * root 3 * root 4 * root 7 * root 8, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 555 := rfl

private theorem nodeClosure_eq_555 : nodeClosure 555 = smallEvenDescentNode 556 := by
  have hi : nodeGeneratorIndex 555 = ![310, 3, 117, 5, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 555 = Subgroup.closure ({word 310, word 3, word 117, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 555)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 2 * root 4 * root 5 * root 7 * root 9, root 8 * root 9, root 2 * root 3 * root 4 * root 7 * root 8, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 556 := rfl

private theorem nodeClosure_eq_556 : nodeClosure 556 = smallEvenDescentNode 557 := by
  have hi : nodeGeneratorIndex 556 = ![161, 355, 115, 1, 5, 5, 5, 5, 5, 5] := rfl
  calc
    nodeClosure 556 = Subgroup.closure ({word 161, word 355, word 115, word 1, word 5} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 556)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 8 * root 9, root 9, root 7 * root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 557 := rfl

private theorem nodeClosure_eq_557 : nodeClosure 557 = smallEvenDescentNode 558 := by
  have hi : nodeGeneratorIndex 557 = ![161, 367, 115, 1, 5, 5, 5, 5, 5, 5] := rfl
  calc
    nodeClosure 557 = Subgroup.closure ({word 161, word 367, word 115, word 1, word 5} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 557)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 2 * root 3 * root 4 * root 8 * root 9, root 9, root 7 * root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 558 := rfl

private theorem nodeClosure_eq_558 : nodeClosure 558 = smallEvenDescentNode 559 := by
  have hi : nodeGeneratorIndex 558 = ![205, 355, 115, 1, 5, 5, 5, 5, 5, 5] := rfl
  calc
    nodeClosure 558 = Subgroup.closure ({word 205, word 355, word 115, word 1, word 5} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 558)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 3 * root 4 * root 5 * root 8 * root 9, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 8 * root 9, root 9, root 7 * root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 559 := rfl

private theorem nodeClosure_eq_559 : nodeClosure 559 = smallEvenDescentNode 560 := by
  have hi : nodeGeneratorIndex 559 = ![205, 367, 115, 1, 5, 5, 5, 5, 5, 5] := rfl
  calc
    nodeClosure 559 = Subgroup.closure ({word 205, word 367, word 115, word 1, word 5} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 559)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 3 * root 4 * root 5 * root 8 * root 9, rootOne ^ 2 * root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 2 * root 3 * root 4 * root 8 * root 9, root 9, root 7 * root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 560 := rfl

private theorem nodeClosure_eq_560 : nodeClosure 560 = smallEvenDescentNode 561 := by
  have hi : nodeGeneratorIndex 560 = ![100, 254, 3, 5, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 560 = Subgroup.closure ({word 100, word 254, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 560)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 561 := rfl

private theorem nodeClosure_eq_561 : nodeClosure 561 = smallEvenDescentNode 562 := by
  have hi : nodeGeneratorIndex 561 = ![100, 333, 3, 5, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 561 = Subgroup.closure ({word 100, word 333, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 561)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 562 := rfl

private theorem nodeClosure_eq_562 : nodeClosure 562 = smallEvenDescentNode 563 := by
  have hi : nodeGeneratorIndex 562 = ![92, 331, 3, 5, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 562 = Subgroup.closure ({word 92, word 331, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 562)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 563 := rfl

private theorem nodeClosure_eq_563 : nodeClosure 563 = smallEvenDescentNode 564 := by
  have hi : nodeGeneratorIndex 563 = ![44, 255, 3, 5, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 563 = Subgroup.closure ({word 44, word 255, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 563)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 5 * root 7 * root 8, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 564 := rfl

private theorem nodeClosure_eq_564 : nodeClosure 564 = smallEvenDescentNode 565 := by
  have hi : nodeGeneratorIndex 564 = ![49, 328, 3, 5, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 564 = Subgroup.closure ({word 49, word 328, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 564)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 565 := rfl

private theorem nodeClosure_eq_565 : nodeClosure 565 = smallEvenDescentNode 566 := by
  have hi : nodeGeneratorIndex 565 = ![49, 258, 3, 5, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 565 = Subgroup.closure ({word 49, word 258, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 565)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 5 * root 6 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 566 := rfl

private theorem nodeClosure_eq_566 : nodeClosure 566 = smallEvenDescentNode 567 := by
  have hi : nodeGeneratorIndex 566 = ![98, 328, 3, 5, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 566 = Subgroup.closure ({word 98, word 328, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 566)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 4 * root 5 * root 7 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 567 := rfl

private theorem nodeClosure_eq_567 : nodeClosure 567 = smallEvenDescentNode 568 := by
  have hi : nodeGeneratorIndex 567 = ![171, 15, 30, 5, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 567 = Subgroup.closure ({word 171, word 15, word 30, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 567)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 3 * root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 568 := rfl

private theorem nodeClosure_eq_568 : nodeClosure 568 = smallEvenDescentNode 569 := by
  have hi : nodeGeneratorIndex 568 = ![312, 122, 3, 5, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 568 = Subgroup.closure ({word 312, word 122, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 568)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 569 := rfl

private theorem nodeClosure_eq_569 : nodeClosure 569 = smallEvenDescentNode 570 := by
  have hi : nodeGeneratorIndex 569 = ![49, 333, 3, 5, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 569 = Subgroup.closure ({word 49, word 333, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 569)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 570 := rfl

private theorem nodeClosure_eq_570 : nodeClosure 570 = smallEvenDescentNode 571 := by
  have hi : nodeGeneratorIndex 570 = ![49, 255, 3, 5, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 570 = Subgroup.closure ({word 49, word 255, word 3, word 5, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 570)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 5 * root 7 * root 8, root 8 * root 9, root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 571 := rfl

private theorem nodeClosure_eq_571 : nodeClosure 571 = smallEvenDescentNode 572 := by
  have hi : nodeGeneratorIndex 571 = ![54, 43, 5, 3, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 571 = Subgroup.closure ({word 54, word 43, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 571)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 5 * root 6 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 572 := rfl

private theorem nodeClosure_eq_572 : nodeClosure 572 = smallEvenDescentNode 573 := by
  have hi : nodeGeneratorIndex 572 = ![49, 34, 5, 3, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 572 = Subgroup.closure ({word 49, word 34, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 572)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 573 := rfl

private theorem nodeClosure_eq_573 : nodeClosure 573 = smallEvenDescentNode 574 := by
  have hi : nodeGeneratorIndex 573 = ![49, 38, 5, 3, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 573 = Subgroup.closure ({word 49, word 38, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 573)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 5, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 574 := rfl

private theorem nodeClosure_eq_574 : nodeClosure 574 = smallEvenDescentNode 575 := by
  have hi : nodeGeneratorIndex 574 = ![182, 12, 4, 17, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 574 = Subgroup.closure ({word 182, word 12, word 4, word 17, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 574)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 5 * root 6 * root 9, root 6 * root 7, root 7, root 5 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 575 := rfl

private theorem nodeClosure_eq_575 : nodeClosure 575 = smallEvenDescentNode 576 := by
  have hi : nodeGeneratorIndex 575 = ![80, 338, 6, 3, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 575 = Subgroup.closure ({word 80, word 338, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 575)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 5 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 576 := rfl

private theorem nodeClosure_eq_576 : nodeClosure 576 = smallEvenDescentNode 577 := by
  have hi : nodeGeneratorIndex 576 = ![80, 330, 6, 3, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 576 = Subgroup.closure ({word 80, word 330, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 576)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 5 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 577 := rfl

private theorem nodeClosure_eq_577 : nodeClosure 577 = smallEvenDescentNode 578 := by
  have hi : nodeGeneratorIndex 577 = ![80, 333, 6, 3, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 577 = Subgroup.closure ({word 80, word 333, word 6, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 577)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 2 * root 5 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 578 := rfl

private theorem nodeClosure_eq_578 : nodeClosure 578 = smallEvenDescentNode 579 := by
  have hi : nodeGeneratorIndex 578 = ![312, 43, 5, 3, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 578 = Subgroup.closure ({word 312, word 43, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 578)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 579 := rfl

private theorem nodeClosure_eq_579 : nodeClosure 579 = smallEvenDescentNode 580 := by
  have hi : nodeGeneratorIndex 579 = ![275, 34, 5, 3, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 579 = Subgroup.closure ({word 275, word 34, word 5, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 579)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 580 := rfl

private theorem nodeClosure_eq_580 : nodeClosure 580 = smallEvenDescentNode 581 := by
  have hi : nodeGeneratorIndex 580 = ![131, 2, 10, 17, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 580 = Subgroup.closure ({word 131, word 2, word 10, word 17, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 580)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 1 * root 5 * root 6 * root 7 * root 8 * root 9, root 8, root 6 * root 8, root 5 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 581 := rfl

private theorem nodeClosure_eq_581 : nodeClosure 581 = smallEvenDescentNode 582 := by
  have hi : nodeGeneratorIndex 581 = ![44, 137, 18, 2, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 581 = Subgroup.closure ({word 44, word 137, word 18, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 581)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, root 1 * root 3 * root 5 * root 7 * root 8 * root 9, root 5 * root 8, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 582 := rfl

private theorem nodeClosure_eq_582 : nodeClosure 582 = smallEvenDescentNode 583 := by
  have hi : nodeGeneratorIndex 582 = ![340, 15, 38, 3, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 582 = Subgroup.closure ({word 340, word 15, word 38, word 3, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 582)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 1 * root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7 * root 8 * root 9, root 4 * root 5, root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 583 := rfl

private theorem nodeClosure_eq_583 : nodeClosure 583 = smallEvenDescentNode 584 := by
  have hi : nodeGeneratorIndex 583 = ![44, 345, 40, 2, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 583 = Subgroup.closure ({word 44, word 345, word 40, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 583)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3, rootOne ^ 2 * root 1 * root 3 * root 5 * root 7 * root 8 * root 9, root 4 * root 5 * root 8 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 584 := rfl

private theorem nodeClosure_eq_584 : nodeClosure 584 = smallEvenDescentNode 585 := by
  have hi : nodeGeneratorIndex 584 = ![46, 348, 40, 2, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 584 = Subgroup.closure ({word 46, word 348, word 40, word 2, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 584)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 3 * root 6 * root 8, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 5 * root 8 * root 9, root 8, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 585 := rfl

private theorem nodeClosure_eq_585 : nodeClosure 585 = smallEvenDescentNode 586 := by
  have hi : nodeGeneratorIndex 585 = ![200, 235, 10, 22, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 585 = Subgroup.closure ({word 200, word 235, word 10, word 22, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 585)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 6 * root 8, root 5 * root 7 * root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 586 := rfl

private theorem nodeClosure_eq_586 : nodeClosure 586 = smallEvenDescentNode 587 := by
  have hi : nodeGeneratorIndex 586 = ![202, 232, 10, 22, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 586 = Subgroup.closure ({word 202, word 232, word 10, word 22, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 586)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 3 * root 4 * root 6 * root 7, root 0 * root 1 * root 2 * root 3 * root 8, root 6 * root 8, root 5 * root 7 * root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 587 := rfl

private theorem nodeClosure_eq_587 : nodeClosure 587 = smallEvenDescentNode 588 := by
  have hi : nodeGeneratorIndex 587 = ![200, 239, 10, 22, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 587 = Subgroup.closure ({word 200, word 239, word 10, word 22, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 587)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 1 * root 2 * root 3 * root 6 * root 7 * root 8 * root 9, root 6 * root 8, root 5 * root 7 * root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 588 := rfl

private theorem nodeClosure_eq_588 : nodeClosure 588 = smallEvenDescentNode 589 := by
  have hi : nodeGeneratorIndex 588 = ![202, 233, 10, 22, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 588 = Subgroup.closure ({word 202, word 233, word 10, word 22, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 588)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 3 * root 4 * root 6 * root 7, root 0 * root 1 * root 2 * root 3 * root 7 * root 8 * root 9, root 6 * root 8, root 5 * root 7 * root 8 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 589 := rfl

private theorem nodeClosure_eq_589 : nodeClosure 589 = smallEvenDescentNode 590 := by
  have hi : nodeGeneratorIndex 589 = ![164, 235, 22, 13, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 589 = Subgroup.closure ({word 164, word 235, word 22, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 589)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 8 * root 9, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 5 * root 7 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 590 := rfl

private theorem nodeClosure_eq_590 : nodeClosure 590 = smallEvenDescentNode 591 := by
  have hi : nodeGeneratorIndex 590 = ![167, 246, 29, 13, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 590 = Subgroup.closure ({word 167, word 246, word 29, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 590)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 7, root 5 * root 6 * root 7 * root 8, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 591 := rfl

private theorem nodeClosure_eq_591 : nodeClosure 591 = smallEvenDescentNode 592 := by
  have hi : nodeGeneratorIndex 591 = ![164, 246, 29, 13, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 591 = Subgroup.closure ({word 164, word 246, word 29, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 591)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 8 * root 9, root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 7, root 5 * root 6 * root 7 * root 8, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 592 := rfl

private theorem nodeClosure_eq_592 : nodeClosure 592 = smallEvenDescentNode 593 := by
  have hi : nodeGeneratorIndex 592 = ![167, 248, 30, 13, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 592 = Subgroup.closure ({word 167, word 248, word 30, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 592)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 7 * root 8, root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 593 := rfl

private theorem nodeClosure_eq_593 : nodeClosure 593 = smallEvenDescentNode 594 := by
  have hi : nodeGeneratorIndex 593 = ![164, 248, 30, 13, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 593 = Subgroup.closure ({word 164, word 248, word 30, word 13, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 593)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 4 * root 8 * root 9, root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7 * root 9, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 594 := rfl

private theorem nodeClosure_eq_594 : nodeClosure 594 = smallEvenDescentNode 595 := by
  have hi : nodeGeneratorIndex 594 = ![194, 141, 30, 12, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 594 = Subgroup.closure ({word 194, word 141, word 30, word 12, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 594)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 595 := rfl

private theorem nodeClosure_eq_595 : nodeClosure 595 = smallEvenDescentNode 596 := by
  have hi : nodeGeneratorIndex 595 = ![190, 141, 30, 12, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 595 = Subgroup.closure ({word 190, word 141, word 30, word 12, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 595)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 4 * root 5 * root 6, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 596 := rfl

private theorem nodeClosure_eq_596 : nodeClosure 596 = smallEvenDescentNode 597 := by
  have hi : nodeGeneratorIndex 596 = ![194, 142, 30, 12, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 596 = Subgroup.closure ({word 194, word 142, word 30, word 12, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 596)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 8, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 597 := rfl

private theorem nodeClosure_eq_597 : nodeClosure 597 = smallEvenDescentNode 598 := by
  have hi : nodeGeneratorIndex 597 = ![191, 138, 30, 12, 1, 1, 1, 1, 1, 1] := rfl
  calc
    nodeClosure 597 = Subgroup.closure ({word 191, word 138, word 30, word 12, word 1} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 597)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 1 * root 3 * root 5 * root 6, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 598 := rfl

private theorem nodeClosure_eq_598 : nodeClosure 598 = smallEvenDescentNode 599 := by
  have hi : nodeGeneratorIndex 598 = ![355, 1, 114, 5, 5, 5, 5, 5, 5, 5] := rfl
  calc
    nodeClosure 598 = Subgroup.closure ({word 355, word 1, word 114, word 5} : Set SylowModel) := by
      change Subgroup.closure (Set.range (word ∘ nodeGeneratorIndex 598)) = _
      rw [Set.range_comp, hi]
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Set.image_insert_eq, Set.image_singleton, Set.insert_eq_of_mem (Set.mem_singleton _)]
    _ = Subgroup.closure ({rootOne ^ 2 * root 0 * root 3, root 9, root 2 * root 3 * root 4 * root 8, root 7 * root 9} : Set SylowModel) := rfl
    _ = smallEvenDescentNode 599 := rfl

/-- The diagnostic word closures are exactly the original nonzero descent nodes. -/
public theorem nodeClosure_eq (i : Fin 599) :
    nodeClosure i = smallEvenDescentNode i.succ := by
  fin_cases i
  · exact nodeClosure_eq_0
  · exact nodeClosure_eq_1
  · exact nodeClosure_eq_2
  · exact nodeClosure_eq_3
  · exact nodeClosure_eq_4
  · exact nodeClosure_eq_5
  · exact nodeClosure_eq_6
  · exact nodeClosure_eq_7
  · exact nodeClosure_eq_8
  · exact nodeClosure_eq_9
  · exact nodeClosure_eq_10
  · exact nodeClosure_eq_11
  · exact nodeClosure_eq_12
  · exact nodeClosure_eq_13
  · exact nodeClosure_eq_14
  · exact nodeClosure_eq_15
  · exact nodeClosure_eq_16
  · exact nodeClosure_eq_17
  · exact nodeClosure_eq_18
  · exact nodeClosure_eq_19
  · exact nodeClosure_eq_20
  · exact nodeClosure_eq_21
  · exact nodeClosure_eq_22
  · exact nodeClosure_eq_23
  · exact nodeClosure_eq_24
  · exact nodeClosure_eq_25
  · exact nodeClosure_eq_26
  · exact nodeClosure_eq_27
  · exact nodeClosure_eq_28
  · exact nodeClosure_eq_29
  · exact nodeClosure_eq_30
  · exact nodeClosure_eq_31
  · exact nodeClosure_eq_32
  · exact nodeClosure_eq_33
  · exact nodeClosure_eq_34
  · exact nodeClosure_eq_35
  · exact nodeClosure_eq_36
  · exact nodeClosure_eq_37
  · exact nodeClosure_eq_38
  · exact nodeClosure_eq_39
  · exact nodeClosure_eq_40
  · exact nodeClosure_eq_41
  · exact nodeClosure_eq_42
  · exact nodeClosure_eq_43
  · exact nodeClosure_eq_44
  · exact nodeClosure_eq_45
  · exact nodeClosure_eq_46
  · exact nodeClosure_eq_47
  · exact nodeClosure_eq_48
  · exact nodeClosure_eq_49
  · exact nodeClosure_eq_50
  · exact nodeClosure_eq_51
  · exact nodeClosure_eq_52
  · exact nodeClosure_eq_53
  · exact nodeClosure_eq_54
  · exact nodeClosure_eq_55
  · exact nodeClosure_eq_56
  · exact nodeClosure_eq_57
  · exact nodeClosure_eq_58
  · exact nodeClosure_eq_59
  · exact nodeClosure_eq_60
  · exact nodeClosure_eq_61
  · exact nodeClosure_eq_62
  · exact nodeClosure_eq_63
  · exact nodeClosure_eq_64
  · exact nodeClosure_eq_65
  · exact nodeClosure_eq_66
  · exact nodeClosure_eq_67
  · exact nodeClosure_eq_68
  · exact nodeClosure_eq_69
  · exact nodeClosure_eq_70
  · exact nodeClosure_eq_71
  · exact nodeClosure_eq_72
  · exact nodeClosure_eq_73
  · exact nodeClosure_eq_74
  · exact nodeClosure_eq_75
  · exact nodeClosure_eq_76
  · exact nodeClosure_eq_77
  · exact nodeClosure_eq_78
  · exact nodeClosure_eq_79
  · exact nodeClosure_eq_80
  · exact nodeClosure_eq_81
  · exact nodeClosure_eq_82
  · exact nodeClosure_eq_83
  · exact nodeClosure_eq_84
  · exact nodeClosure_eq_85
  · exact nodeClosure_eq_86
  · exact nodeClosure_eq_87
  · exact nodeClosure_eq_88
  · exact nodeClosure_eq_89
  · exact nodeClosure_eq_90
  · exact nodeClosure_eq_91
  · exact nodeClosure_eq_92
  · exact nodeClosure_eq_93
  · exact nodeClosure_eq_94
  · exact nodeClosure_eq_95
  · exact nodeClosure_eq_96
  · exact nodeClosure_eq_97
  · exact nodeClosure_eq_98
  · exact nodeClosure_eq_99
  · exact nodeClosure_eq_100
  · exact nodeClosure_eq_101
  · exact nodeClosure_eq_102
  · exact nodeClosure_eq_103
  · exact nodeClosure_eq_104
  · exact nodeClosure_eq_105
  · exact nodeClosure_eq_106
  · exact nodeClosure_eq_107
  · exact nodeClosure_eq_108
  · exact nodeClosure_eq_109
  · exact nodeClosure_eq_110
  · exact nodeClosure_eq_111
  · exact nodeClosure_eq_112
  · exact nodeClosure_eq_113
  · exact nodeClosure_eq_114
  · exact nodeClosure_eq_115
  · exact nodeClosure_eq_116
  · exact nodeClosure_eq_117
  · exact nodeClosure_eq_118
  · exact nodeClosure_eq_119
  · exact nodeClosure_eq_120
  · exact nodeClosure_eq_121
  · exact nodeClosure_eq_122
  · exact nodeClosure_eq_123
  · exact nodeClosure_eq_124
  · exact nodeClosure_eq_125
  · exact nodeClosure_eq_126
  · exact nodeClosure_eq_127
  · exact nodeClosure_eq_128
  · exact nodeClosure_eq_129
  · exact nodeClosure_eq_130
  · exact nodeClosure_eq_131
  · exact nodeClosure_eq_132
  · exact nodeClosure_eq_133
  · exact nodeClosure_eq_134
  · exact nodeClosure_eq_135
  · exact nodeClosure_eq_136
  · exact nodeClosure_eq_137
  · exact nodeClosure_eq_138
  · exact nodeClosure_eq_139
  · exact nodeClosure_eq_140
  · exact nodeClosure_eq_141
  · exact nodeClosure_eq_142
  · exact nodeClosure_eq_143
  · exact nodeClosure_eq_144
  · exact nodeClosure_eq_145
  · exact nodeClosure_eq_146
  · exact nodeClosure_eq_147
  · exact nodeClosure_eq_148
  · exact nodeClosure_eq_149
  · exact nodeClosure_eq_150
  · exact nodeClosure_eq_151
  · exact nodeClosure_eq_152
  · exact nodeClosure_eq_153
  · exact nodeClosure_eq_154
  · exact nodeClosure_eq_155
  · exact nodeClosure_eq_156
  · exact nodeClosure_eq_157
  · exact nodeClosure_eq_158
  · exact nodeClosure_eq_159
  · exact nodeClosure_eq_160
  · exact nodeClosure_eq_161
  · exact nodeClosure_eq_162
  · exact nodeClosure_eq_163
  · exact nodeClosure_eq_164
  · exact nodeClosure_eq_165
  · exact nodeClosure_eq_166
  · exact nodeClosure_eq_167
  · exact nodeClosure_eq_168
  · exact nodeClosure_eq_169
  · exact nodeClosure_eq_170
  · exact nodeClosure_eq_171
  · exact nodeClosure_eq_172
  · exact nodeClosure_eq_173
  · exact nodeClosure_eq_174
  · exact nodeClosure_eq_175
  · exact nodeClosure_eq_176
  · exact nodeClosure_eq_177
  · exact nodeClosure_eq_178
  · exact nodeClosure_eq_179
  · exact nodeClosure_eq_180
  · exact nodeClosure_eq_181
  · exact nodeClosure_eq_182
  · exact nodeClosure_eq_183
  · exact nodeClosure_eq_184
  · exact nodeClosure_eq_185
  · exact nodeClosure_eq_186
  · exact nodeClosure_eq_187
  · exact nodeClosure_eq_188
  · exact nodeClosure_eq_189
  · exact nodeClosure_eq_190
  · exact nodeClosure_eq_191
  · exact nodeClosure_eq_192
  · exact nodeClosure_eq_193
  · exact nodeClosure_eq_194
  · exact nodeClosure_eq_195
  · exact nodeClosure_eq_196
  · exact nodeClosure_eq_197
  · exact nodeClosure_eq_198
  · exact nodeClosure_eq_199
  · exact nodeClosure_eq_200
  · exact nodeClosure_eq_201
  · exact nodeClosure_eq_202
  · exact nodeClosure_eq_203
  · exact nodeClosure_eq_204
  · exact nodeClosure_eq_205
  · exact nodeClosure_eq_206
  · exact nodeClosure_eq_207
  · exact nodeClosure_eq_208
  · exact nodeClosure_eq_209
  · exact nodeClosure_eq_210
  · exact nodeClosure_eq_211
  · exact nodeClosure_eq_212
  · exact nodeClosure_eq_213
  · exact nodeClosure_eq_214
  · exact nodeClosure_eq_215
  · exact nodeClosure_eq_216
  · exact nodeClosure_eq_217
  · exact nodeClosure_eq_218
  · exact nodeClosure_eq_219
  · exact nodeClosure_eq_220
  · exact nodeClosure_eq_221
  · exact nodeClosure_eq_222
  · exact nodeClosure_eq_223
  · exact nodeClosure_eq_224
  · exact nodeClosure_eq_225
  · exact nodeClosure_eq_226
  · exact nodeClosure_eq_227
  · exact nodeClosure_eq_228
  · exact nodeClosure_eq_229
  · exact nodeClosure_eq_230
  · exact nodeClosure_eq_231
  · exact nodeClosure_eq_232
  · exact nodeClosure_eq_233
  · exact nodeClosure_eq_234
  · exact nodeClosure_eq_235
  · exact nodeClosure_eq_236
  · exact nodeClosure_eq_237
  · exact nodeClosure_eq_238
  · exact nodeClosure_eq_239
  · exact nodeClosure_eq_240
  · exact nodeClosure_eq_241
  · exact nodeClosure_eq_242
  · exact nodeClosure_eq_243
  · exact nodeClosure_eq_244
  · exact nodeClosure_eq_245
  · exact nodeClosure_eq_246
  · exact nodeClosure_eq_247
  · exact nodeClosure_eq_248
  · exact nodeClosure_eq_249
  · exact nodeClosure_eq_250
  · exact nodeClosure_eq_251
  · exact nodeClosure_eq_252
  · exact nodeClosure_eq_253
  · exact nodeClosure_eq_254
  · exact nodeClosure_eq_255
  · exact nodeClosure_eq_256
  · exact nodeClosure_eq_257
  · exact nodeClosure_eq_258
  · exact nodeClosure_eq_259
  · exact nodeClosure_eq_260
  · exact nodeClosure_eq_261
  · exact nodeClosure_eq_262
  · exact nodeClosure_eq_263
  · exact nodeClosure_eq_264
  · exact nodeClosure_eq_265
  · exact nodeClosure_eq_266
  · exact nodeClosure_eq_267
  · exact nodeClosure_eq_268
  · exact nodeClosure_eq_269
  · exact nodeClosure_eq_270
  · exact nodeClosure_eq_271
  · exact nodeClosure_eq_272
  · exact nodeClosure_eq_273
  · exact nodeClosure_eq_274
  · exact nodeClosure_eq_275
  · exact nodeClosure_eq_276
  · exact nodeClosure_eq_277
  · exact nodeClosure_eq_278
  · exact nodeClosure_eq_279
  · exact nodeClosure_eq_280
  · exact nodeClosure_eq_281
  · exact nodeClosure_eq_282
  · exact nodeClosure_eq_283
  · exact nodeClosure_eq_284
  · exact nodeClosure_eq_285
  · exact nodeClosure_eq_286
  · exact nodeClosure_eq_287
  · exact nodeClosure_eq_288
  · exact nodeClosure_eq_289
  · exact nodeClosure_eq_290
  · exact nodeClosure_eq_291
  · exact nodeClosure_eq_292
  · exact nodeClosure_eq_293
  · exact nodeClosure_eq_294
  · exact nodeClosure_eq_295
  · exact nodeClosure_eq_296
  · exact nodeClosure_eq_297
  · exact nodeClosure_eq_298
  · exact nodeClosure_eq_299
  · exact nodeClosure_eq_300
  · exact nodeClosure_eq_301
  · exact nodeClosure_eq_302
  · exact nodeClosure_eq_303
  · exact nodeClosure_eq_304
  · exact nodeClosure_eq_305
  · exact nodeClosure_eq_306
  · exact nodeClosure_eq_307
  · exact nodeClosure_eq_308
  · exact nodeClosure_eq_309
  · exact nodeClosure_eq_310
  · exact nodeClosure_eq_311
  · exact nodeClosure_eq_312
  · exact nodeClosure_eq_313
  · exact nodeClosure_eq_314
  · exact nodeClosure_eq_315
  · exact nodeClosure_eq_316
  · exact nodeClosure_eq_317
  · exact nodeClosure_eq_318
  · exact nodeClosure_eq_319
  · exact nodeClosure_eq_320
  · exact nodeClosure_eq_321
  · exact nodeClosure_eq_322
  · exact nodeClosure_eq_323
  · exact nodeClosure_eq_324
  · exact nodeClosure_eq_325
  · exact nodeClosure_eq_326
  · exact nodeClosure_eq_327
  · exact nodeClosure_eq_328
  · exact nodeClosure_eq_329
  · exact nodeClosure_eq_330
  · exact nodeClosure_eq_331
  · exact nodeClosure_eq_332
  · exact nodeClosure_eq_333
  · exact nodeClosure_eq_334
  · exact nodeClosure_eq_335
  · exact nodeClosure_eq_336
  · exact nodeClosure_eq_337
  · exact nodeClosure_eq_338
  · exact nodeClosure_eq_339
  · exact nodeClosure_eq_340
  · exact nodeClosure_eq_341
  · exact nodeClosure_eq_342
  · exact nodeClosure_eq_343
  · exact nodeClosure_eq_344
  · exact nodeClosure_eq_345
  · exact nodeClosure_eq_346
  · exact nodeClosure_eq_347
  · exact nodeClosure_eq_348
  · exact nodeClosure_eq_349
  · exact nodeClosure_eq_350
  · exact nodeClosure_eq_351
  · exact nodeClosure_eq_352
  · exact nodeClosure_eq_353
  · exact nodeClosure_eq_354
  · exact nodeClosure_eq_355
  · exact nodeClosure_eq_356
  · exact nodeClosure_eq_357
  · exact nodeClosure_eq_358
  · exact nodeClosure_eq_359
  · exact nodeClosure_eq_360
  · exact nodeClosure_eq_361
  · exact nodeClosure_eq_362
  · exact nodeClosure_eq_363
  · exact nodeClosure_eq_364
  · exact nodeClosure_eq_365
  · exact nodeClosure_eq_366
  · exact nodeClosure_eq_367
  · exact nodeClosure_eq_368
  · exact nodeClosure_eq_369
  · exact nodeClosure_eq_370
  · exact nodeClosure_eq_371
  · exact nodeClosure_eq_372
  · exact nodeClosure_eq_373
  · exact nodeClosure_eq_374
  · exact nodeClosure_eq_375
  · exact nodeClosure_eq_376
  · exact nodeClosure_eq_377
  · exact nodeClosure_eq_378
  · exact nodeClosure_eq_379
  · exact nodeClosure_eq_380
  · exact nodeClosure_eq_381
  · exact nodeClosure_eq_382
  · exact nodeClosure_eq_383
  · exact nodeClosure_eq_384
  · exact nodeClosure_eq_385
  · exact nodeClosure_eq_386
  · exact nodeClosure_eq_387
  · exact nodeClosure_eq_388
  · exact nodeClosure_eq_389
  · exact nodeClosure_eq_390
  · exact nodeClosure_eq_391
  · exact nodeClosure_eq_392
  · exact nodeClosure_eq_393
  · exact nodeClosure_eq_394
  · exact nodeClosure_eq_395
  · exact nodeClosure_eq_396
  · exact nodeClosure_eq_397
  · exact nodeClosure_eq_398
  · exact nodeClosure_eq_399
  · exact nodeClosure_eq_400
  · exact nodeClosure_eq_401
  · exact nodeClosure_eq_402
  · exact nodeClosure_eq_403
  · exact nodeClosure_eq_404
  · exact nodeClosure_eq_405
  · exact nodeClosure_eq_406
  · exact nodeClosure_eq_407
  · exact nodeClosure_eq_408
  · exact nodeClosure_eq_409
  · exact nodeClosure_eq_410
  · exact nodeClosure_eq_411
  · exact nodeClosure_eq_412
  · exact nodeClosure_eq_413
  · exact nodeClosure_eq_414
  · exact nodeClosure_eq_415
  · exact nodeClosure_eq_416
  · exact nodeClosure_eq_417
  · exact nodeClosure_eq_418
  · exact nodeClosure_eq_419
  · exact nodeClosure_eq_420
  · exact nodeClosure_eq_421
  · exact nodeClosure_eq_422
  · exact nodeClosure_eq_423
  · exact nodeClosure_eq_424
  · exact nodeClosure_eq_425
  · exact nodeClosure_eq_426
  · exact nodeClosure_eq_427
  · exact nodeClosure_eq_428
  · exact nodeClosure_eq_429
  · exact nodeClosure_eq_430
  · exact nodeClosure_eq_431
  · exact nodeClosure_eq_432
  · exact nodeClosure_eq_433
  · exact nodeClosure_eq_434
  · exact nodeClosure_eq_435
  · exact nodeClosure_eq_436
  · exact nodeClosure_eq_437
  · exact nodeClosure_eq_438
  · exact nodeClosure_eq_439
  · exact nodeClosure_eq_440
  · exact nodeClosure_eq_441
  · exact nodeClosure_eq_442
  · exact nodeClosure_eq_443
  · exact nodeClosure_eq_444
  · exact nodeClosure_eq_445
  · exact nodeClosure_eq_446
  · exact nodeClosure_eq_447
  · exact nodeClosure_eq_448
  · exact nodeClosure_eq_449
  · exact nodeClosure_eq_450
  · exact nodeClosure_eq_451
  · exact nodeClosure_eq_452
  · exact nodeClosure_eq_453
  · exact nodeClosure_eq_454
  · exact nodeClosure_eq_455
  · exact nodeClosure_eq_456
  · exact nodeClosure_eq_457
  · exact nodeClosure_eq_458
  · exact nodeClosure_eq_459
  · exact nodeClosure_eq_460
  · exact nodeClosure_eq_461
  · exact nodeClosure_eq_462
  · exact nodeClosure_eq_463
  · exact nodeClosure_eq_464
  · exact nodeClosure_eq_465
  · exact nodeClosure_eq_466
  · exact nodeClosure_eq_467
  · exact nodeClosure_eq_468
  · exact nodeClosure_eq_469
  · exact nodeClosure_eq_470
  · exact nodeClosure_eq_471
  · exact nodeClosure_eq_472
  · exact nodeClosure_eq_473
  · exact nodeClosure_eq_474
  · exact nodeClosure_eq_475
  · exact nodeClosure_eq_476
  · exact nodeClosure_eq_477
  · exact nodeClosure_eq_478
  · exact nodeClosure_eq_479
  · exact nodeClosure_eq_480
  · exact nodeClosure_eq_481
  · exact nodeClosure_eq_482
  · exact nodeClosure_eq_483
  · exact nodeClosure_eq_484
  · exact nodeClosure_eq_485
  · exact nodeClosure_eq_486
  · exact nodeClosure_eq_487
  · exact nodeClosure_eq_488
  · exact nodeClosure_eq_489
  · exact nodeClosure_eq_490
  · exact nodeClosure_eq_491
  · exact nodeClosure_eq_492
  · exact nodeClosure_eq_493
  · exact nodeClosure_eq_494
  · exact nodeClosure_eq_495
  · exact nodeClosure_eq_496
  · exact nodeClosure_eq_497
  · exact nodeClosure_eq_498
  · exact nodeClosure_eq_499
  · exact nodeClosure_eq_500
  · exact nodeClosure_eq_501
  · exact nodeClosure_eq_502
  · exact nodeClosure_eq_503
  · exact nodeClosure_eq_504
  · exact nodeClosure_eq_505
  · exact nodeClosure_eq_506
  · exact nodeClosure_eq_507
  · exact nodeClosure_eq_508
  · exact nodeClosure_eq_509
  · exact nodeClosure_eq_510
  · exact nodeClosure_eq_511
  · exact nodeClosure_eq_512
  · exact nodeClosure_eq_513
  · exact nodeClosure_eq_514
  · exact nodeClosure_eq_515
  · exact nodeClosure_eq_516
  · exact nodeClosure_eq_517
  · exact nodeClosure_eq_518
  · exact nodeClosure_eq_519
  · exact nodeClosure_eq_520
  · exact nodeClosure_eq_521
  · exact nodeClosure_eq_522
  · exact nodeClosure_eq_523
  · exact nodeClosure_eq_524
  · exact nodeClosure_eq_525
  · exact nodeClosure_eq_526
  · exact nodeClosure_eq_527
  · exact nodeClosure_eq_528
  · exact nodeClosure_eq_529
  · exact nodeClosure_eq_530
  · exact nodeClosure_eq_531
  · exact nodeClosure_eq_532
  · exact nodeClosure_eq_533
  · exact nodeClosure_eq_534
  · exact nodeClosure_eq_535
  · exact nodeClosure_eq_536
  · exact nodeClosure_eq_537
  · exact nodeClosure_eq_538
  · exact nodeClosure_eq_539
  · exact nodeClosure_eq_540
  · exact nodeClosure_eq_541
  · exact nodeClosure_eq_542
  · exact nodeClosure_eq_543
  · exact nodeClosure_eq_544
  · exact nodeClosure_eq_545
  · exact nodeClosure_eq_546
  · exact nodeClosure_eq_547
  · exact nodeClosure_eq_548
  · exact nodeClosure_eq_549
  · exact nodeClosure_eq_550
  · exact nodeClosure_eq_551
  · exact nodeClosure_eq_552
  · exact nodeClosure_eq_553
  · exact nodeClosure_eq_554
  · exact nodeClosure_eq_555
  · exact nodeClosure_eq_556
  · exact nodeClosure_eq_557
  · exact nodeClosure_eq_558
  · exact nodeClosure_eq_559
  · exact nodeClosure_eq_560
  · exact nodeClosure_eq_561
  · exact nodeClosure_eq_562
  · exact nodeClosure_eq_563
  · exact nodeClosure_eq_564
  · exact nodeClosure_eq_565
  · exact nodeClosure_eq_566
  · exact nodeClosure_eq_567
  · exact nodeClosure_eq_568
  · exact nodeClosure_eq_569
  · exact nodeClosure_eq_570
  · exact nodeClosure_eq_571
  · exact nodeClosure_eq_572
  · exact nodeClosure_eq_573
  · exact nodeClosure_eq_574
  · exact nodeClosure_eq_575
  · exact nodeClosure_eq_576
  · exact nodeClosure_eq_577
  · exact nodeClosure_eq_578
  · exact nodeClosure_eq_579
  · exact nodeClosure_eq_580
  · exact nodeClosure_eq_581
  · exact nodeClosure_eq_582
  · exact nodeClosure_eq_583
  · exact nodeClosure_eq_584
  · exact nodeClosure_eq_585
  · exact nodeClosure_eq_586
  · exact nodeClosure_eq_587
  · exact nodeClosure_eq_588
  · exact nodeClosure_eq_589
  · exact nodeClosure_eq_590
  · exact nodeClosure_eq_591
  · exact nodeClosure_eq_592
  · exact nodeClosure_eq_593
  · exact nodeClosure_eq_594
  · exact nodeClosure_eq_595
  · exact nodeClosure_eq_596
  · exact nodeClosure_eq_597
  · exact nodeClosure_eq_598

end ReeTwo.SylowModel.SmallEvenDescentEdges
