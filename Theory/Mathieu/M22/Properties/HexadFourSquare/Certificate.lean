module

public import Theory.Mathieu.M22.Properties.HexadSplitCoordinates.Splitting
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.RepresentativeKernel.Data

/-!
# A native square-root pair in a point complement

Two words in the certified degree-22 generators give a square root `root` and
an involution `second`. The square of the root and the second involution
preserve the standard hexad and fix point zero outside it. They generate a
four-group, and the root commutes with the second involution.

Word evaluation is checked once against explicit permutation tables; all
remaining identities are small kernel reductions on those tables. Carrier
membership follows from the generator words, without an abstract group-model
comparison. The words can be rediscovered by `source/discover.py`.

This is the native local calculation used in the complement-lifting step of
Aschbacher--Smith I.2.2(6), printed p.412 / PDF p.423. `HexadFourSquare` transports
it to the actual point-defined section of every native hexad.
-/

public section
open scoped Pointwise
namespace Sporadic.Mathieu.M22HexadFourSquare.Certificate

open M22RepresentativeKernel

private def rootTable : Fin 22 → Fin 22 :=
  ![12, 4, 14, 7, 2, 13, 3, 10, 21, 19, 6, 17, 0, 15, 1, 16, 5, 11, 18, 8, 20, 9]

private def rootInvTable : Fin 22 → Fin 22 :=
  ![12, 14, 4, 6, 1, 16, 10, 3, 19, 21, 7, 17, 0, 5, 2, 13, 15, 11, 18, 9, 20, 8]

private def rootPerm : Equiv.Perm (Fin 22) where
  toFun := rootTable
  invFun := rootInvTable
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem root_word : (wordElement [2, 0, 2, 0, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2]).val = rootPerm := by
  apply Equiv.ext
  intro x
  rw [wordElement_apply]
  change wordAction [2, 0, 2, 0, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2] x = rootTable x
  revert x
  decide +kernel

noncomputable def root : M22 :=
  ⟨rootPerm, root_word ▸ (wordElement [2, 0, 2, 0, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2]).property⟩

private theorem root_apply (x : Fin 22) : root.val x = rootTable x := rfl

private def secondTable : Fin 22 → Fin 22 :=
  ![0, 3, 10, 1, 7, 21, 14, 4, 16, 13, 2, 11, 12, 9, 6, 19, 8, 17, 18, 15, 20, 5]

private def secondInvTable : Fin 22 → Fin 22 :=
  ![0, 3, 10, 1, 7, 21, 14, 4, 16, 13, 2, 11, 12, 9, 6, 19, 8, 17, 18, 15, 20, 5]

private def secondPerm : Equiv.Perm (Fin 22) where
  toFun := secondTable
  invFun := secondInvTable
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem second_word : (wordElement [0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 0, 1]).val = secondPerm := by
  apply Equiv.ext
  intro x
  rw [wordElement_apply]
  change wordAction [0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 0, 1] x = secondTable x
  revert x
  decide +kernel

noncomputable def second : M22 :=
  ⟨secondPerm, second_word ▸ (wordElement [0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 0, 1]).property⟩

private theorem second_apply (x : Fin 22) : second.val x = secondTable x := rfl

private theorem square_mem : root ^ 2 ∈ MulAction.stabilizer M22 m22Hexad123 := by
  apply MulAction.mem_stabilizer_finset'.mpr
  intro x hx
  change root.val (root.val x) ∈ m22Hexad123
  rw [root_apply, root_apply]
  revert x
  decide +kernel

private theorem second_mem : second ∈ MulAction.stabilizer M22 m22Hexad123 := by
  apply MulAction.mem_stabilizer_finset'.mpr
  intro x hx
  change second.val x ∈ m22Hexad123
  rw [second_apply]
  revert x
  decide +kernel

noncomputable def firstInHexad : MulAction.stabilizer M22 m22Hexad123 :=
  ⟨root ^ 2, square_mem⟩

noncomputable def secondInHexad : MulAction.stabilizer M22 m22Hexad123 :=
  ⟨second, second_mem⟩

theorem first_square : firstInHexad ^ 2 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change root.val (root.val (root.val (root.val x))) = x
  simp only [root_apply]
  revert x
  decide +kernel

theorem second_square : secondInHexad ^ 2 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change second.val (second.val x) = x
  simp only [second_apply]
  revert x
  decide +kernel

theorem first_ne_one : firstInHexad ≠ 1 := by
  intro h
  have hh := congrArg (fun g : MulAction.stabilizer M22 m22Hexad123 => g.val.val 1) h
  change root.val (root.val 1) = 1 at hh
  simp only [root_apply] at hh
  exact (by decide : rootTable (rootTable 1) ≠ 1) hh

theorem second_ne_one : secondInHexad ≠ 1 := by
  intro h
  have hh := congrArg (fun g : MulAction.stabilizer M22 m22Hexad123 => g.val.val 1) h
  change second.val 1 = 1 at hh
  rw [second_apply] at hh
  exact (by decide : secondTable 1 ≠ 1) hh

theorem product_ne_one : firstInHexad * secondInHexad ≠ 1 := by
  intro h
  have hh := congrArg (fun g : MulAction.stabilizer M22 m22Hexad123 => g.val.val 1) h
  change root.val (root.val (second.val 1)) = 1 at hh
  simp only [root_apply, second_apply] at hh
  exact (by decide : rootTable (rootTable (secondTable 1)) ≠ 1) hh

theorem first_fixes : firstInHexad.val • (0 : Fin 22) = 0 := by
  change root.val (root.val 0) = 0
  simp only [root_apply]
  decide

theorem second_fixes : secondInHexad.val • (0 : Fin 22) = 0 := by
  change second.val 0 = 0
  rw [second_apply]
  decide

theorem root_square : root ^ 2 = firstInHexad.val := by
  unfold firstInHexad
  rfl

theorem root_commutes : Commute root secondInHexad.val := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change root.val (second.val x) = second.val (root.val x)
  simp only [root_apply, second_apply]
  revert x
  decide +kernel

end Sporadic.Mathieu.M22HexadFourSquare.Certificate
