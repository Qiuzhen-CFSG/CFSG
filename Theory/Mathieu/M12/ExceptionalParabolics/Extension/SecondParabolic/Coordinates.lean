module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Seeds
public import Theory.GroupTheory.QuaternionSwapModel.MarkedSylow.SecondParabolic

/-!
# Compatible quaternion coordinates in the degree-24 outer extension

The quaternion factors are re-marked, with left basis `(leftI, leftJ⁻¹)`
and right basis `((rightJ * rightI)⁻¹, rightJ)`. An explicit outer involution
swaps these bases. Their paired second generator is the original natural
involution `v`, and their common square is the original `z`. A second
involution gives the literal whole-overlap twist, and an explicit actor
has the four prescribed actions on the elementary sixteen.

All finite identities below are checked by the Lean kernel. The coordinate
maps retain the actual permutation embedding; no parabolic core is identified
with the swap subgroup. Source: Aschbacher--Smith, 14.2.21, printed p.988,
and the ATLAS degree-24 generators documented in `Extension.Seeds`.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.SecondCoordinates
open QuaternionSwapModel
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def leftIPerm : Equiv.Perm (Fin 24) :=
  List.formPerm [1, 13, 14, 18] *
  List.formPerm [2, 7, 23, 22] *
  List.formPerm [4, 21] *
  List.formPerm [5, 10, 17, 20] *
  List.formPerm [6, 15, 12, 11] *
  List.formPerm [16, 0]

def leftJPerm : Equiv.Perm (Fin 24) :=
  List.formPerm [1, 2, 14, 23] *
  List.formPerm [4, 0] *
  List.formPerm [5, 11, 17, 15] *
  List.formPerm [6, 10, 12, 20] *
  List.formPerm [7, 13, 22, 18] *
  List.formPerm [16, 21]

def rightIPerm : Equiv.Perm (Fin 24) :=
  List.formPerm [1, 7, 14, 22] *
  List.formPerm [2, 13, 23, 18] *
  List.formPerm [3, 8] *
  List.formPerm [5, 6, 17, 12] *
  List.formPerm [9, 19] *
  List.formPerm [10, 15, 20, 11]

def rightJPerm : Equiv.Perm (Fin 24) :=
  List.formPerm [1, 2, 14, 23] *
  List.formPerm [3, 9] *
  List.formPerm [5, 15, 17, 11] *
  List.formPerm [6, 10, 12, 20] *
  List.formPerm [7, 18, 22, 13] *
  List.formPerm [8, 19]

def swapPerm : Equiv.Perm (Fin 24) :=
  List.formPerm [1, 6] *
  List.formPerm [2, 10] *
  List.formPerm [3, 4] *
  List.formPerm [5, 18] *
  List.formPerm [7, 15] *
  List.formPerm [8, 21] *
  List.formPerm [9, 0] *
  List.formPerm [11, 22] *
  List.formPerm [12, 14] *
  List.formPerm [13, 17] *
  List.formPerm [16, 19] *
  List.formPerm [20, 23]

def extraPerm : Equiv.Perm (Fin 24) :=
  List.formPerm [2, 23] *
  List.formPerm [5, 11] *
  List.formPerm [6, 12] *
  List.formPerm [7, 18] *
  List.formPerm [8, 19] *
  List.formPerm [13, 22] *
  List.formPerm [15, 17] *
  List.formPerm [16, 21]

def actorPerm : Equiv.Perm (Fin 24) :=
  List.formPerm [1, 5, 19, 6, 13, 21] *
  List.formPerm [2, 11, 3, 10, 7, 0] *
  List.formPerm [4, 23, 15, 9, 20, 22] *
  List.formPerm [8, 12, 18, 16, 14, 17]

theorem leftIPerm_eq : leftIPerm = ((leftI : Carrier) : Equiv.Perm (Fin 24)) := by
  decide +kernel

def markedLeftI : Carrier := ⟨leftIPerm, leftIPerm_eq ▸ (leftI : Carrier).property⟩

theorem leftJPerm_eq : leftJPerm = ((leftJ⁻¹ : Carrier) : Equiv.Perm (Fin 24)) := by
  decide +kernel

def markedLeftJ : Carrier := ⟨leftJPerm, leftJPerm_eq ▸ (leftJ⁻¹ : Carrier).property⟩

theorem rightIPerm_eq : rightIPerm = (((rightJ * rightI)⁻¹ : Carrier) : Equiv.Perm (Fin 24)) := by
  decide +kernel

def markedRightI : Carrier := ⟨rightIPerm, rightIPerm_eq ▸ ((rightJ * rightI)⁻¹ : Carrier).property⟩

theorem rightJPerm_eq : rightJPerm = ((rightJ : Carrier) : Equiv.Perm (Fin 24)) := by
  decide +kernel

def markedRightJ : Carrier := ⟨rightJPerm, rightJPerm_eq ▸ (rightJ : Carrier).property⟩

private def outerWord : List (Fin 3) → Carrier
  | [] => 1
  | i :: w => (if i = 0 then ⟨generatorA, Subgroup.subset_closure (by simp)⟩
      else if i = 1 then ⟨generatorB, Subgroup.subset_closure (by simp)⟩
      else (⟨generatorB, Subgroup.subset_closure (by simp)⟩ : Carrier)⁻¹) * outerWord w

theorem swapPerm_mem : swapPerm ∈ group := by
  have h : swapPerm = (outerWord [0, 1, 0, 2, 0, 1, 0, 2, 0, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0] : Equiv.Perm (Fin 24)) := by decide +kernel
  exact h ▸ (outerWord [0, 1, 0, 2, 0, 1, 0, 2, 0, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0]).property

def swap : Carrier := ⟨swapPerm, swapPerm_mem⟩

theorem extraPerm_mem : extraPerm ∈ group := by
  have h : extraPerm = ((rightJ⁻¹ * rightI⁻¹ * movingActor⁻¹ * leftI⁻¹ *
      movingActor⁻¹ * rightJ⁻¹ : Carrier) : Equiv.Perm (Fin 24)) := by decide +kernel
  exact h ▸ (rightJ⁻¹ * rightI⁻¹ * movingActor⁻¹ * leftI⁻¹ * movingActor⁻¹ * rightJ⁻¹).property

def extra : Carrier := ⟨extraPerm, extraPerm_mem⟩

theorem actorPerm_mem : actorPerm ∈ group := by
  have h : actorPerm = ((swap * leftI⁻¹ * movingActor * leftI⁻¹ * leftJ⁻¹ : Carrier) :
      Equiv.Perm (Fin 24)) := by decide +kernel
  exact h ▸ (swap * leftI⁻¹ * movingActor * leftI⁻¹ * leftJ⁻¹).property

def actor : Carrier := ⟨actorPerm, actorPerm_mem⟩

def quaternionValue (i j : Carrier) : QuaternionGroup 2 → Carrier
  | .a n => i ^ n.val
  | .xa n => j * i ^ n.val

def leftMap : QuaternionGroup 2 →* Carrier where
  toFun := quaternionValue markedLeftI markedLeftJ
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def rightMap : QuaternionGroup 2 →* Carrier where
  toFun := quaternionValue markedRightI markedRightJ
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def rawValue (w : Raw) : Carrier :=
  leftMap (w.left 1) * rightMap (w.left turn) * (if w.right = 1 then 1 else swap)

theorem left_right_commute (q r : QuaternionGroup 2) :
    leftMap q * rightMap r = rightMap r * leftMap q := by
  have h : ∀ q r : QuaternionGroup 2, leftMap q * rightMap r = rightMap r * leftMap q := by
    decide +kernel
  exact h q r

theorem swap_left (q : QuaternionGroup 2) : swap * leftMap q = rightMap q * swap := by
  have h : ∀ q : QuaternionGroup 2, swap * leftMap q = rightMap q * swap := by decide +kernel
  exact h q

theorem swap_right (q : QuaternionGroup 2) : swap * rightMap q = leftMap q * swap := by
  have h : ∀ q : QuaternionGroup 2, swap * rightMap q = leftMap q * swap := by decide +kernel
  exact h q

theorem swap_square : swap * swap = 1 := by decide +kernel

end Sporadic.Mathieu.M12ExceptionalExtension.SecondCoordinates
