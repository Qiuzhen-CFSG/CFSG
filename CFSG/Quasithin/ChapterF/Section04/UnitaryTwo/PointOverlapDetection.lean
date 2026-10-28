module
public import Theory.GroupTheory.AutomorphismOddIndexDetection
public import Theory.GroupTheory.PCorePrimeToIndex
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.PointCore
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour.BinaryOrders

/-!
# The ordinary flag detects automorphisms of the unitary point group

The literal flag overlap has index three in the point parabolic. It therefore
contains the point two-core. An automorphism fixing the overlap pointwise has
central displacement in the center of that self-centralizing core. This center
is central of order two, so odd-index detection makes the automorphism trivial.

This is the action-comparison input when extending the ordinary point map to
the doubled amalgam in Aschbacher--Smith 13.5.17, printed p.922.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.PointOverlapDetection
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
local notation "P" => pointParabolic 1 hn
local notation "B" => Subgroup.subgroupOf (overlap 1 hn) P

theorem overlap_index : (B).index = 3 := by
  have h := (B).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe
    (show overlap 1 hn ≤ P by rw [← exact_overlap]; exact inf_le_left)).toEquiv,
    BinaryCompletion.middle_card, BinaryCompletion.point_card] at h
  omega

theorem core_le_overlap : pCore 2 P ≤ B :=
  (pCore_le_map_pCore_of_prime_not_dvd_index B
    (by rw [overlap_index]; decide)).trans (map_subtype_le _)

/-- Pointwise fixation of the actual embedded flag overlap detects every
automorphism of the ordinary point endpoint. -/
theorem eq_one_of_fixes_overlap (α : MulAut P)
    (hfix : ∀ x ∈ B, α x = x) : α = 1 :=
  MulAut.eq_one_of_fixed_odd_index_overgroup (pCore 2 P) B core_le_overlap
    PointCore.projective_point_core_selfCentralizing PointCore.rootSubgroup_central
    (by rw [PointCore.projective_point_core_center_card])
    (by rw [overlap_index]; decide) α hfix

/-- Two point automorphisms agreeing on the literal overlap agree everywhere. -/
theorem eq_of_eq_on_overlap (α β : MulAut P)
    (h : ∀ x ∈ B, α x = β x) : α = β := by
  have he := eq_one_of_fixes_overlap (α.trans β.symm) (by
    intro x hx
    change β.symm (α x) = x
    rw [h x hx, β.symm_apply_apply])
  apply MulEquiv.ext
  intro x
  have hx := DFunLike.congr_fun he x
  change β.symm (α x) = x at hx
  exact β.symm.injective (hx.trans (β.symm_apply_apply x).symm)

end CFSG.Quasithin.ChapterF.UnitaryTwo.PointOverlapDetection
