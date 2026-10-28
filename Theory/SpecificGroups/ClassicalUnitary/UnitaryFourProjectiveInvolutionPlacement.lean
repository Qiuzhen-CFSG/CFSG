module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourInvolutionPlacement
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.PlainFusion
/-!
# Projective transport of unitary involution placement

The matrix placement theorem transfers through the faithful projectivization map.
Every involution in the actual projective upper Sylow is conjugate in the point
parabolic to the image of the plane two-core. This is a literal map statement,
not an abstract identification of involution classes.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.InvolutionPlacement
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
local notation "L" => L2 1 hn

def planeCore : Subgroup (ProjectiveGroup 1 hn) := (pCore 2 L).map (L2 1 hn).subtype

theorem matrix_plane_core_map :
    ((pCore 2 (L2Matrix 1 hn)).map (L2Matrix 1 hn).subtype).map (projection 1 hn) = planeCore := by
  have he : (L2 1 hn).subtype.comp (L2ProjectIso 1 hn).toMonoidHom =
      (projection 1 hn).comp (L2Matrix 1 hn).subtype := rfl
  rw [planeCore, ← pCore_map_iso 2 (L2ProjectIso 1 hn)]
  simp only [map_map, he]

theorem projective_sylow_involution_placement
    (a : ProjectiveGroup 1 hn) (ha : a ∈ upperProjective 1 hn) (ha2 : a ^ 2 = 1) :
    ∃ g : pointParabolic 1 hn, g.val * a * g.val⁻¹ ∈ planeCore := by
  obtain ⟨a,ha,rfl⟩ := ha
  have hsq : a ^ 2 = 1 := (projection_injective 1 hn) (by simpa only [map_pow, map_one] using ha2)
  obtain ⟨g,hg⟩ := Theory.SpecificGroups.ClassicalUnitary.UnitaryFourInvolutionPlacement.upper_involution_point_conjugate_plane
    (MatrixField 1) (fieldConj 1) (fieldConj_involutive 1 hn) a ha hsq
  refine ⟨⟨projection 1 hn g.val, ⟨g.val,g.property,rfl⟩⟩, ?_⟩
  let gM : MatrixGroup 1 hn := g.val
  have hm : gM * a * gM⁻¹ ∈
      (pCore 2 (L2Matrix 1 hn)).map (L2Matrix 1 hn).subtype := by
    rw [← L2MatrixRadical_eq_twoCore]
    exact hg
  have hh := mem_map_of_mem (projection 1 hn) hm
  rw [matrix_plane_core_map] at hh
  simpa only [map_mul,map_inv] using hh
end CFSG.Quasithin.ChapterF.UnitaryTwo.InvolutionPlacement
