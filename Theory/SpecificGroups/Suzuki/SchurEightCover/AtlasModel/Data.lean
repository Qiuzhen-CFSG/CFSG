module

public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.Checks

/-!
# Checked permutations for the Suzuki cover candidate

The numerical tables define actual permutations: the first, third and fourth
are involutions, and the second has fourth power one. All four inverse
identities are checked in Lean's kernel on the 2080 points.
Source data, action conventions and attribution are in `source/README.md`.
-/

@[expose] public section
namespace BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.Data

private theorem aFun_involutive : Function.Involutive aFun := by
  apply of_checkPoints
  decide +kernel

private theorem bFun_fourth (p : Point) : bFun (bFun (bFun (bFun p))) = p := by
  apply of_checkPoints _ p
  decide +kernel

private theorem zFun_involutive : Function.Involutive zFun := by
  apply of_checkPoints
  decide +kernel

private theorem wFun_involutive : Function.Involutive wFun := by
  apply of_checkPoints
  decide +kernel

def a : Equiv.Perm Point where
  toFun := aFun
  invFun := aFun
  left_inv := by exact aFun_involutive
  right_inv := by exact aFun_involutive

def b : Equiv.Perm Point where
  toFun := bFun
  invFun := fun p => bFun (bFun (bFun p))
  left_inv := by exact bFun_fourth
  right_inv := by exact bFun_fourth

def z : Equiv.Perm Point where
  toFun := zFun
  invFun := zFun
  left_inv := by exact zFun_involutive
  right_inv := by exact zFun_involutive

def w : Equiv.Perm Point where
  toFun := wFun
  invFun := wFun
  left_inv := by exact wFun_involutive
  right_inv := by exact wFun_involutive

theorem a_sq : a ^ 2 = 1 := by
  apply Equiv.ext
  exact aFun_involutive

theorem b_fourth : b ^ 4 = 1 := by
  apply Equiv.ext
  exact bFun_fourth

theorem z_sq : z * z = 1 := Equiv.ext zFun_involutive
theorem w_sq : w * w = 1 := Equiv.ext wFun_involutive

end BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.Data
