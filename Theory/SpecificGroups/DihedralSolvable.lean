module
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Solvable
public import Mathlib.Tactic.NormNum

/-!
# Solvability of dihedral groups

Every dihedral group is solvable, including the infinite model at parameter
zero. Rotations form an abelian normal subgroup, and reflection parity maps
onto the abelian group of order two with exactly that kernel. Solvability
is preserved by this extension.

This standalone theorem is extracted from the Chapter 5 alternating-group
development, preserving its existing public name. It supplies the dihedral
case in the PSL2 section exclusion needed by ABG II.3 Lemma 2, without
importing the unrelated alternating-group classification machinery.
-/

namespace GLS3.Chapter5

/-- Every dihedral group is solvable. -/
public theorem dihedralGroup_isSolvable (n : Nat) : Group.IsSolvable (DihedralGroup n) := by
  let rotations : Multiplicative (ZMod n) →* DihedralGroup n := {
    toFun i := DihedralGroup.r i.toAdd
    map_one' := DihedralGroup.r_zero
    map_mul' i j := by simp }
  let parity : DihedralGroup n →* Multiplicative (ZMod 2) := {
    toFun
      | DihedralGroup.r _ => 1
      | DihedralGroup.sr _ => Multiplicative.ofAdd 1
    map_one' := rfl
    map_mul' a b := by
      cases a <;> cases b <;> simp
      change (0 : ZMod 2) = 1 + 1
      exact (ZMod.natCast_self 2).symm }
  apply Group.isSolvable_of_ker_le_range rotations parity
  intro g hg
  cases g with
  | r i => exact ⟨Multiplicative.ofAdd i, rfl⟩
  | sr i =>
      change Multiplicative.ofAdd (1 : ZMod 2) = 1 at hg
      have : (1 : ZMod 2) = 0 := congrArg Multiplicative.toAdd hg
      norm_num at this

end GLS3.Chapter5

