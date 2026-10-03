module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenDescentNodes
public import Theory.SpecificGroups.ReeTwo.TailQuotientOrder16Nodes

/-!
# Size bounds for the ten nonzero large descent nodes

Explicit words put all six tail roots in each of nodes 1 through 10.
Four more word certificates put one of the checked order-sixteen quotient
nodes in each image under the tail projection. Since the tail has index 64
in the Sylow group, the image has index at most four, and each original
node therefore has at least 1024 elements.

Source: the Shinoda (1975), (2.3), pp. 81–82 root coordinates and the checked
order-sixteen subgroups in `TailQuotientOrder16Nodes`. The proposed words
are verified by kernel reduction; external calculations are not proof inputs.
-/

namespace ReeTwo.SylowModel.SmallEvenLargeNodes
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration
open TailQuotient
set_option maxRecDepth 10000
private def idx (i : Fin 10) : Fin 600 := ⟨i.val + 1, by omega⟩
private def gen (i : Fin 10) : Fin 10 → SylowModel :=
![![rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9], ![rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9], ![rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9], ![rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 1 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9], ![rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9], ![rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 1 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9], ![rootOne ^ 2 * root 0 * root 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9], ![root 0, rootOne ^ 2 * root 0 * root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9], ![root 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9], ![root 0, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9]] i

private theorem generated (i : Fin 10) :
    smallEvenDescentNode (idx i) = Subgroup.closure (Set.range (gen i)) := by
  fin_cases i <;>
    simp only [gen, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union] <;> rfl

private def tailWords (i : Fin 10) : Fin 6 → List (Fin 10) :=
![![[7, 5], [4, 4, 4, 6, 3], [6], [9, 3, 3], [9, 8], [9]], ![[7, 5], [4, 4, 4, 6, 3], [6], [9, 3, 3], [9, 8], [9]], ![[7, 5], [4, 4, 4, 6, 3], [6], [9, 3, 3], [9, 8], [9]], ![[7, 5], [4, 4, 4, 6, 3], [6], [9, 3, 3], [9, 8], [9]], ![[7, 5], [4, 4, 4, 6, 3], [6], [9, 3, 3], [9, 8], [9]], ![[7, 5], [4, 4, 4, 6, 3], [6], [9, 3, 3], [9, 8], [9]], ![[7, 5], [4, 4, 4, 6, 3], [6], [9, 3, 3], [9, 8], [9]], ![[7, 5], [4, 4, 4, 6, 3], [6], [9, 3, 3], [9, 8], [9]], ![[7, 5], [4, 4, 4, 6, 3], [6], [7, 0, 0], [0, 0], [9]], ![[7, 5], [4, 4, 4, 6, 3], [6], [9, 3, 3], [9, 8], [9]]] i

set_option maxHeartbeats 4000000 in
private theorem tail_valid : ∀ i j,
    evalWord (gen i) (tailWords i j) = root (j.natAdd 4) := by decide +kernel

private theorem tail_le (i : Fin 10) : tailSubgroup ≤ smallEvenDescentNode (idx i) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, hj, rfl⟩
  change 4 ≤ j.val at hj
  let k : Fin 6 := ⟨j.val - 4, by omega⟩
  have he : k.natAdd 4 = j := Fin.ext (by dsimp [k]; omega)
  rw [← he, ← tail_valid i k, generated]
  exact evalWord_mem _ _ (fun l => Subgroup.subset_closure (Set.mem_range_self l)) _

private def quotientNode (i : Fin 10) : Fin 27 :=
![3, 8, 16, 1, 18, 10, 17, 6, 7, 0] i

private def quotientWords (i : Fin 10) : Fin 4 → List (Fin 10) :=
![![[0, 2], [0, 1, 3], [2], []], ![[0, 1, 2], [0, 1, 3], [0], []], ![[2, 1], [0, 1, 3], [0], []], ![[0, 2], [0, 1], [2], []], ![[1, 2, 3], [1], [0], []], ![[0, 1], [1, 2], [0], []], ![[1, 0, 2], [0, 1], [1], []], ![[0], [2, 3], [1, 0, 2], []], ![[0, 2], [0, 3], [0], [1]], ![[0], [0, 1, 2, 3], [0, 1], [0, 1, 3]]] i

set_option maxHeartbeats 4000000 in
private theorem quotient_valid : ∀ i j,
    projection (evalWord (gen i) (quotientWords i j)) =
      Order16Nodes.generator (quotientNode i) j := by
  intro i j
  apply coordinateCode_injective
  exact (by decide +kernel : ∀ i j,
    coordinateCode (projection (evalWord (gen i) (quotientWords i j))) =
      coordinateCode (Order16Nodes.generator (quotientNode i) j)) i j

private theorem quotient_le (i : Fin 10) :
    Order16Nodes.node (quotientNode i) ≤
      (smallEvenDescentNode (idx i)).map projection := by
  rw [Order16Nodes.node_eq_closure]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  rw [← quotient_valid i j]
  apply Subgroup.mem_map_of_mem
  rw [generated]
  exact evalWord_mem _ _ (fun l => Subgroup.subset_closure (Set.mem_range_self l)) _

private theorem large (i : Fin 10) : 1024 ≤ Nat.card (smallEvenDescentNode (idx i)) := by
  let U := smallEvenDescentNode (idx i)
  have hc : 16 ≤ Nat.card (U.map projection) := by
    simpa only [Order16Nodes.node_card] using Subgroup.card_le_of_le (quotient_le i)
  have hi := U.index_map_eq projection_surjective (ker_projection ▸ tail_le i)
  have hq := (U.map projection).index_mul_card
  rw [hi, TailQuotient.card] at hq
  have hib : U.index ≤ 4 := by nlinarith
  have hu := U.index_mul_card
  rw [SylowModel.card] at hu
  nlinarith [Nat.mul_le_mul_right (Nat.card U) hib]

/-- All ten nonzero indices reserved for large nodes have the required size. -/
public theorem nonzero_large (i : Fin 600) (hpos : 0 < i.val) (hlt : i.val < 11) :
    1024 ≤ Nat.card (smallEvenDescentNode i) := by
  let j : Fin 10 := ⟨i.val - 1, by omega⟩
  have he : idx j = i := Fin.ext (by dsimp [idx, j]; omega)
  rw [← he]
  exact large j

end ReeTwo.SylowModel.SmallEvenLargeNodes
