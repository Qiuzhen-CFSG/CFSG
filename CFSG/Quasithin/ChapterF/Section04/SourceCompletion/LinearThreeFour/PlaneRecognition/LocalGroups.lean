module

public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeFour.Basic
public import Theory.SpecificGroups.PSL3Four.CentralCover.FullPlaneNormalizer

/-!
# The literal completion is perfect

At field order four each full projective parabolic equals its affine local
factor. The existing affine perfectness theorem therefore makes both marked
endpoint images perfect. Their prescribed generation proves that the whole
completion is perfect, without any geometric, order, or simplicity premise.
In particular every homomorphism from the completion to a solvable group is
trivial. This is the input that will exclude the diagonal and field factors
when comparing its plane action with PSL₃(4).

The endpoint orders are transported from the existing native parabolic count.
Source: the PSL₃(4) specialization of Aschbacher–Smith F.4.8(2), p.278.
-/

public section

namespace CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour.Completion
open Subgroup Matrix.PSL3.LinearThree
local notation "F" => Matrix.PSL3Four.F
variable {G : Type*} [Group G] (c : Completion G)

private theorem native_parabolic_card (b : Bool) :
    Nat.card (Matrix.PSL3.RootPlaneGeometry.parabolic F b) = 960 := by
  have h := Matrix.PSL3Four.FullPlaneNormalizer.parabolic_card
    (MonoidHom.id Matrix.PSL3Four.PSL) Function.surjective_id b
  simpa using h

/-- The actual left endpoint image has order 960. -/
theorem left_card_eq : Nat.card c.left.range = 960 :=
  (Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion.left_card c).trans
    (native_parabolic_card true)

/-- The actual right endpoint image has order 960. -/
theorem right_card_eq : Nat.card c.right.range = 960 :=
  (Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion.right_card c).trans
    (native_parabolic_card false)

/-- Perfectness transported along the literal point-parabolic embedding. -/
theorem left_isPerfect : Group.IsPerfect c.left.range := by
  have hp : pointParabolic F = pointLocal F :=
    Matrix.PSL3Four.ElementaryParabolic.native_parabolic_eq_local true
  let : Group.IsPerfect (pointParabolic F) := by
    rw [hp]
    exact pointLocal_isPerfect F (by rw [Matrix.PSL3Four.card_F])
  exact Group.IsPerfect.range c.left

/-- Perfectness transported along the literal line-parabolic embedding. -/
theorem right_isPerfect : Group.IsPerfect c.right.range := by
  have hp : lineParabolic F = lineLocal F :=
    Matrix.PSL3Four.ElementaryParabolic.native_parabolic_eq_local false
  let : Group.IsPerfect (lineParabolic F) := by
    rw [hp]
    exact lineLocal_isPerfect F (by rw [Matrix.PSL3Four.card_F])
  exact Group.IsPerfect.range c.right

include c

/-- Generation by the two perfect endpoints makes every completion perfect. -/
theorem isPerfect : Group.IsPerfect G := by
  let := c.left_isPerfect
  let := c.right_isPerfect
  refine ⟨top_unique ?_⟩
  rw [← c.generated]
  apply sup_le
  · rw [← commutator_eq_self (H := c.left.range)]
    exact Subgroup.commutator_mono le_top le_top
  · rw [← commutator_eq_self (H := c.right.range)]
    exact Subgroup.commutator_mono le_top le_top

/-- Every solvable image of this actual completion is trivial. -/
theorem solvable_image_eq_one {H : Type*} [Group H] [Group.IsSolvable H]
    (f : G →* H) (g : G) : f g = 1 := by
  let := c.isPerfect
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hs : Subsingleton f.range := by
    by_contra h
    let : Nontrivial f.range := not_subsingleton_iff_nontrivial.mp h
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  exact congrArg Subtype.val (hs.elim (f.rangeRestrict g) 1)
end CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour.Completion
