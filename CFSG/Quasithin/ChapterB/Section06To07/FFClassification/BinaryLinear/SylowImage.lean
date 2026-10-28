module
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.UniqueMaximal
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.NormalSupplementModels

/-!
# Minimal-parabolic images in binary linear groups

Every nonsolvable image of a minimal parabolic is again minimal parabolic.
If its prescribed Sylow maps onto a full binary linear Sylow, the image is
therefore a unique-maximal Sylow overgroup. The flag calculation makes it
solvable, a contradiction. The map may have an arbitrary kernel.

The original H-star application in LocalConfigurationNaturalHStarSourceProperLinear
constructs the map and checks the full Sylow image using the chosen natural
module. Source: Aschbacher--Smith, 12.2.7, printed pp.797--798.
-/

public noncomputable section
open Subgroup
open BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.ChapterB
variable {A : Type*} [Group A] [Finite A] {n : ℕ}
/-- A full ambient Sylow image forces the minimal-parabolic image to be solvable. -/
theorem minimalParabolic_image_solvable_binary
    (hn : 0 < n) (T : Sylow 2 A) (hP : IsMinimalParabolicOver T ⊤)
    (f : A →* LinearGroup n) (S : Sylow 2 (LinearGroup n))
    (hS : (T : Subgroup A).map f = (S : Subgroup _)) : Group.IsSolvable f.range := by
  let : Finite (LinearGroup n) := Finite.of_injective
    (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective
  by_contra hs
  have hp := minimalParabolic_surjective_of_not_solvable T hP
    f.rangeRestrict f.rangeRestrict_surjective hs
  have hu := hasUniqueMaximalOver_map_subtype hp.1
  have he : ((T.mapSurjective f.rangeRestrict_surjective : Sylow 2 f.range) :
      Subgroup f.range).map f.range.subtype = (S : Subgroup _) := by
    change ((T : Subgroup A).map f.rangeRestrict).map f.range.subtype = _
    rw [Subgroup.map_map]
    exact hS
  rw [he] at hu
  apply hs
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact BinaryLinear.SylowFlagOvergroups.solvable_of_uniqueMaximal S f.range hu
/-- The original three-or-five interface, retained as a specialization. -/
theorem minimalParabolic_image_solvable_binary_three_or_five
    (hn : n = 3 ∨ n = 5) (T : Sylow 2 A) (hP : IsMinimalParabolicOver T ⊤)
    (f : A →* LinearGroup n) (S : Sylow 2 (LinearGroup n))
    (hS : (T : Subgroup A).map f = (S : Subgroup _)) : Group.IsSolvable f.range :=
  minimalParabolic_image_solvable_binary (by omega) T hP f S hS
end CFSG.Quasithin.ChapterB
