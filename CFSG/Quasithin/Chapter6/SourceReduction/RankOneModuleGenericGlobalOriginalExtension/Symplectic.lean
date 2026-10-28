module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.SymplecticCore
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionCatalogue

/-!
# Removing the original symplectic extension

The supplied broad marking permits outer automorphisms in both original
endpoints; it marks their residuals, their inner intersections and their
whole overlap. Nonsolvability first excludes the binary field. The native
quotient/core restriction and the original normalized right Borel give S≤R.
Generation across the full overlap then removes both endpoint outer parts.

Restricting the same maps gives both inclusion squares to the native
point/plane amalgam, in either orientation. Its left quotient fixes m=n>1
and identifies both natural blocks. The Chapter 12 application works for
every preparation and perfect selected R before the residual of H is known.
The shared DGS assembly still owns construction and exhaustiveness of the
broad markings; this module supplies the symplectic source-specific reduction.

Source: Aschbacher--Smith F.1.12, pp.263--264, and 5.2.6, pp.650--651
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
namespace OriginalSymplectic
open Theory.SpecificGroups.SymplecticFour
variable (F : Type) [Field F] [Finite F] [CharP F 2] (point : Bool)

/-- Both native orientations retain the whole flag Borel. -/
@[expose] def orientedAmalgam : RankTwoAmalgam (parabolic F point)
    (borel (F := F)) (parabolic F (!point)) := by
  apply RankTwoAmalgam.ofSubgroups
  · cases point
    · exact inf_le_right
    · exact inf_le_left
  · cases point
    · exact inf_le_left
    · exact inf_le_right

variable {G : Type*} [Group G] (L R S : Subgroup G)

/-- Mark both residuals and inner intersections in the full automorphism group. -/
abbrev Marking := OriginalExtension.Marking L R S
  (localFactor F point) (localFactor F (!point))
  (parabolic F point) (parabolic F (!point))

private def intersectionIso : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic F point)
      (parabolic F point ⊓ parabolic F (!point)) (parabolic F (!point))
      inf_le_left inf_le_right) (orientedAmalgam F point) := by
  have he : parabolic F point ⊓ parabolic F (!point) = borel (F := F) := by
    cases point
    · change planeParabolic ⊓ pointParabolic = _
      rw [inf_comm]
      exact ChapterF.GreenBook.LieModels.SymplecticFour.overlap_eq
    · exact ChapterF.GreenBook.LieModels.SymplecticFour.overlap_eq
  exact { left := MulEquiv.refl _
          right := MulEquiv.refl _
          middle := MulEquiv.subgroupCongr he
          left_commutes := fun _ => Subtype.ext rfl
          right_commutes := fun _ => Subtype.ext rfl }
end OriginalSymplectic

namespace Preparation
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (F : Type) [Field F] [Finite F] [CharP F 2]
  {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m) (point : Bool)
  (e : OriginalSymplectic.Marking F point L R (sourceS L H))

omit [Finite F] [CharP F 2] in
include d h hTH hp e in
private theorem original_symplectic_right_marking :
    (R.subgroupOf (ChapterF.Source.parabolic ![L,R] (sourceS L H) 1)).map e.right =
      (OriginalSymplectic.localFactor F (!point)).map MulAut.conj := by
  have he := d.original_local_eq_residual h hTH hp 1
  change R.subgroupOf (ChapterF.Source.parabolic ![L,R] (sourceS L H) 1) = _ at he
  rw [he]
  exact e.right_residual

include d h hTH hp hm hF e

/-- Nonsolvability excludes the binary field before any extension collapse. -/
theorem original_symplectic_parameter : 1 < m :=
  d.symplectic_extension_parameter h hTH F (!point) e.right e.right_injective
    (d.original_symplectic_right_marking h hTH hp F point e) hp hm hF

/-- The native core calculation and normalized Borel place the same source S in R. -/
theorem sourceS_le_right_of_original_symplectic : sourceS L H ≤ R :=
  d.sourceS_le_right_of_symplectic_extension h hTH F
    (d.original_symplectic_parameter h hTH hp F hm hF point e) hF (!point)
    e.right e.right_injective (d.original_symplectic_right_marking h hTH hp F point e)

/-- Both full endpoints have inner image, with all odd overlap elements retained. -/
theorem original_symplectic_endpoints_inner :
    e.left.range ≤ MulAut.innerSubgroup (Sp F) ∧
    e.right.range ≤ MulAut.innerSubgroup (Sp F) :=
  d.original_extension_endpoints_inner h hTH hp e
    (d.sourceS_le_right_of_original_symplectic h hTH hp F hm hF point e)

/-- Construct the compatible comparison by restricting the supplied marking. -/
def originalSymplecticComparison : RankTwoAmalgam.Iso
    (sourceParabolicAmalgam ![L,R] (sourceS L H))
      (OriginalSymplectic.orientedAmalgam F point) :=
  (e.restrict
    (Theory.GroupTheory.conj_injective_of_center_eq_bot EvenProjective.center_eq_bot)
    (d.original_symplectic_endpoints_inner h hTH hp F hm hF point e)).trans
      (OriginalSymplectic.intersectionIso F point)

/-- The actual symplectic catalogue row follows from the broad original extension. -/
theorem concreteComparison_of_original_symplectic :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) := by
  apply ConcreteAmalgamComparison.symplectic F m hm hF
  have he := d.originalSymplecticComparison h hTH hp F hm hF point e
  cases point
  · exact Or.inr ⟨he⟩
  · exact Or.inl ⟨he⟩

/-- The original left quotient identifies the field and both actual natural blocks. -/
theorem original_symplectic_field_and_blocks :
    m = n ∧ 1 < m ∧ ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n := by
  have he := d.originalSymplecticComparison h hTH hp F hm hF point e
  have hc : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,R] (sourceS L H))
        (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,R] (sourceS L H))
        (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse) := by
    cases point
    · exact Or.inr ⟨he⟩
    · exact Or.inl ⟨he⟩
  obtain ⟨hmn,hL,hR⟩ := d.symplectic_amalgam_blocks h hTH hp F hm hF hc
  exact ⟨hmn,hmn ▸ h.exponent,hL,hR⟩

theorem originalSymplecticComparison_left_apply
    (x : ChapterF.Source.parabolic ![L,R] (sourceS L H) 0) :
    MulAut.conj ((d.originalSymplecticComparison h hTH hp F hm hF point e).left x).val = e.left x :=
  e.restrict_left_apply _ _ x

theorem originalSymplecticComparison_right_apply
    (x : ChapterF.Source.parabolic ![L,R] (sourceS L H) 1) :
    MulAut.conj ((d.originalSymplecticComparison h hTH hp F hm hF point e).right x).val = e.right x :=
  e.restrict_right_apply _ _ x

theorem originalSymplecticComparison_middle_apply
    (x : (ChapterF.Source.parabolic ![L,R] (sourceS L H) 0 ⊓
      ChapterF.Source.parabolic ![L,R] (sourceS L H) 1 : Subgroup G)) :
    MulAut.conj ((d.originalSymplecticComparison h hTH hp F hm hF point e).middle x).val =
      e.left ((sourceParabolicAmalgam ![L,R] (sourceS L H)).left x) :=
  e.restrict_middle_apply _ _ x
end Preparation

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
