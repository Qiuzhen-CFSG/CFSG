module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.PointCore
public import Theory.GroupTheory.Amalgam.RankTwoCompletion
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The actual Sylow image in a unitary-four completion

In a faithful completion of the concrete U4(2) amalgam, embedded in a finite
ambient group, the source centralizer bound on its central root involution
promotes the chosen local Sylow to an ambient Sylow. The standard overlap
Sylow is carried by the completion's actual middle map. Compatibility of the
two endpoint maps is retained in the completion; no alternate abstract Sylow
identification replaces the marked image.

Source: Aschbacher--Smith F.4.33 and F.4.34(1), printed p.291.
This is the plain U4(2) case; graph extensions and final recognition are
separate source arguments.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.UnitaryTwo
open GreenBook.LieModels.UnitaryFour PointCore
open Theory.GroupTheory
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]

theorem completion_point_sylow
    (c : RankTwoAmalgam.FaithfulCompletion (amalgam 1 (Nat.le_refl 1)) (G := G0))
    (i : G0 →* G) (hi : Function.Injective i)
    (z : pointParabolic 1 (Nat.le_refl 1)) (hz : orderOf z = 2)
    (hzc : z ∈ center (pointParabolic 1 (Nat.le_refl 1)))
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range)
    (T : Sylow 2 (pointParabolic 1 (Nat.le_refl 1))) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = (T : Subgroup _).map (i.comp c.left) :=
  sylow_map_of_center_two_core (i.comp c.left) (hi.comp c.left_injective)
    projective_point_core_center_card projective_point_core_selfCentralizing z hz hzc hc T

theorem completion_middle_sylow
    (c : RankTwoAmalgam.FaithfulCompletion (amalgam 1 (Nat.le_refl 1)) (G := G0))
    (i : G0 →* G) (hi : Function.Injective i)
    (z : pointParabolic 1 (Nat.le_refl 1)) (hz : orderOf z = 2)
    (hzc : z ∈ center (pointParabolic 1 (Nat.le_refl 1)))
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range) :
    ∃ S : Sylow 2 G, (S : Subgroup G) =
      ((projectiveSylow 1 (Nat.le_refl 1)).subtype
        (upperProjective_le_overlap 1 (Nat.le_refl 1)) : Subgroup _).map (i.comp c.middle) := by
  let T := (projectiveSylow 1 (Nat.le_refl 1)).subtype
    (projectiveSylow_le_parabolics 1 (Nat.le_refl 1)).1
  obtain ⟨S,hS⟩ := completion_point_sylow c i hi z hz hzc hc T
  refine ⟨S, hS.trans ?_⟩
  apply le_antisymm
  · rintro x ⟨a, ha, rfl⟩
    have haU : a.val ∈ upperProjective 1 (Nat.le_refl 1) := ha
    exact ⟨⟨a, upperProjective_le_overlap 1 (Nat.le_refl 1) haU⟩, haU, rfl⟩
  · rintro x ⟨a, ha, rfl⟩
    exact ⟨(amalgam 1 (Nat.le_refl 1)).left a, ha, rfl⟩


/-- Source F.4.33 with the actual center-of-core root marking and middle map. -/
theorem source_plain_sylow
    (c : RankTwoAmalgam.FaithfulCompletion (amalgam 1 (Nat.le_refl 1)) (G := G0))
    (i : G0 →* G) (hi : Function.Injective i)
    (z : pointParabolic 1 (Nat.le_refl 1)) (hz : orderOf z = 2)
    (hzroot : z ∈ rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range) :
    ∃ S : Sylow 2 G, (S : Subgroup G) =
      ((projectiveSylow 1 (Nat.le_refl 1)).subtype
        (upperProjective_le_overlap 1 (Nat.le_refl 1)) : Subgroup _).map (i.comp c.middle) :=
  completion_middle_sylow c i hi z hz (rootSubgroup_central hzroot) hc

/-- The same source bound identifies the centralizer and root normalizer. -/
theorem source_plain_root_normalizer
    (c : RankTwoAmalgam.FaithfulCompletion (amalgam 1 (Nat.le_refl 1)) (G := G0))
    (i : G0 →* G) (z : pointParabolic 1 (Nat.le_refl 1))
    (hz : orderOf (i (c.left z)) = 2) (hzroot : z ∈ rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range) :
    centralizer ({i (c.left z)} : Set G) = (i.comp c.left).range ∧
      normalizer (zpowers (i (c.left z)) : Set G) = (i.comp c.left).range := by
  have he : centralizer ({i (c.left z)} : Set G) = (i.comp c.left).range := by
    apply le_antisymm hc
    rintro x ⟨a, rfl⟩
    exact mem_centralizer_singleton_iff.mpr (by
      simpa only [MonoidHom.comp_apply, map_mul] using
        congrArg (i.comp c.left) (mem_center_iff.mp (rootSubgroup_central hzroot) a))
  exact ⟨he, (normalizer_zpowers_eq_centralizer_of_order_two _ hz).trans he⟩

end CFSG.Quasithin.ChapterF.UnitaryTwo
