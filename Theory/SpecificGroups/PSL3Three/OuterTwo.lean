module

public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeSquares
public import Theory.SpecificGroups.PSL3Three.Simplicity
public import Mathlib.GroupTheory.PGroup

/-!
# The outer automorphism group of PSL₃(3) is a two-group

The determinant kernel acts by inner automorphisms, so the diagonal outer
image is a quotient of a subgroup of the two-element unit group of F₃.
Every outer square belongs to that image by the proved prime-field
linear/graph coverage. This proves the intrinsic model assertion used in
Aschbacher--Smith, 2.5.8(1), printed p.556.
-/

public section
open scoped MatrixGroups
namespace Matrix.PSL3Three
open PSL3.OuterSolvable

/-- The diagonal outer image over F₃ is a two-group. -/
theorem innerDiagonalOuter_isTwoGroup :
    IsPGroup 2 (innerDiagonalOuter (ZMod 3)) := by
  have hu : IsPGroup 2 (ZMod 3)ˣ := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_units, Nat.card_zmod]; norm_num)
  let d : GL (Fin 3) (ZMod 3) →* (ZMod 3)ˣ := GeneralLinearGroup.det
  let f := linearOuterAction (ZMod 3)
  have hq : IsPGroup 2 (GL (Fin 3) (ZMod 3) ⧸ d.ker) :=
    hu.of_injective (QuotientGroup.kerLift d) (QuotientGroup.kerLift_injective d)
  have hk : d.ker ≤ f.rangeRestrict.ker := by
    simpa only [MonoidHom.ker_rangeRestrict] using
      det_ker_le_linearOuterAction_ker (ZMod 3)
  exact hq.of_surjective (QuotientGroup.lift d.ker f.rangeRestrict hk)
    (QuotientGroup.lift_surjective_of_surjective d.ker f.rangeRestrict
      f.rangeRestrict_surjective hk)

/-- The actual outer automorphism quotient of PSL₃(3) is a two-group. -/
theorem outer_isTwoGroup : IsPGroup 2 (MulAut.Outer PSL(3, ZMod 3)) := by
  let := isSimpleGroup_psl3_three
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup PSL(3, ZMod 3)) x
  have hs := OddPrimeSquares.outer_square_mem not_isSolvable_psl3_three
    (by norm_num : Nat.Prime 3) (by decide : Odd 3) (by simp) a
  obtain ⟨n, hn⟩ := innerDiagonalOuter_isTwoGroup ⟨_, hs⟩
  refine ⟨n + 1, ?_⟩
  have hh := congrArg Subtype.val hn
  change ((_ : MulAut.Outer PSL(3, ZMod 3)) ^ 2) ^ (2 ^ n) = 1 at hh
  rw [← pow_mul] at hh
  simpa only [pow_succ'] using hh

end Matrix.PSL3Three
