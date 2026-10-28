module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.G2Core
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionCatalogue
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2Maximal

/-!
# Removing the original G₂ extension

The supplied original marking permits outer automorphisms at both endpoints.
The marked short local first excludes the binary field. Faithful core-center
action forces the long-first orientation. The short right-local core theorem
and original normalized Borel then give S≤R; generation across the full
original overlap makes both endpoints inner.

Restriction through the same faithful conjugation map constructs both
inclusion squares, retaining the entire Borel. The original left quotient
identifies the field order with 2^n, and both source factors contain S.
The Chapter 12 application feeds the result to residual preparation for every
perfect selected R. Broad marked classification and final recognition remain
with their existing source owners.

Source: Aschbacher--Smith F.1.12, pp.263--264, and 5.2.6, pp.650--651
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
namespace OriginalG2
open Atlas.G2 Atlas.G2.LieParabolicSetup
variable (F : Type) [Field F] (short : Bool)

@[expose] def localFactor : Subgroup (Model F) := if short then local₁ else local₂
@[expose] def parabolic : Subgroup (Model F) := if short then parabolic₁ else parabolic₂

/-- The literal orientation of the native pair, retaining the full Borel. -/
@[expose] def orientedAmalgam : RankTwoAmalgam (parabolic F short)
    (borel (K := F)) (parabolic F (!short)) := by
  apply RankTwoAmalgam.ofSubgroups
  · cases short
    · exact borel_le_parabolic₂
    · exact borel_le_parabolic₁
  · cases short
    · exact borel_le_parabolic₁
    · exact borel_le_parabolic₂

variable {G : Type*} [Group G] (L R S : Subgroup G)

/-- Broad markings of the residuals, inner intersections, and whole overlap. -/
abbrev Marking := OriginalExtension.Marking L R S
  (localFactor F short) (localFactor F (!short))
  (parabolic F short) (parabolic F (!short))

private def intersectionIso : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic F short)
      (parabolic F short ⊓ parabolic F (!short)) (parabolic F (!short))
      inf_le_left inf_le_right) (orientedAmalgam F short) := by
  have he : parabolic F short ⊓ parabolic F (!short) = borel (K := F) := by
    cases short
    · change parabolic₂ ⊓ parabolic₁ = _
      rw [inf_comm]
      exact parabolics_intersection
    · exact parabolics_intersection
  exact { left := MulEquiv.refl _
          right := MulEquiv.refl _
          middle := MulEquiv.subgroupCongr he
          left_commutes := fun _ => Subtype.ext rfl
          right_commutes := fun _ => Subtype.ext rfl }
end OriginalG2

namespace Preparation
open Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.LieAutomorphismExtensions
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (F : Type) [Field F] [Finite F] [CharP F 2] (short : Bool)
  (e : OriginalG2.Marking F short L R (sourceS L H))
include d h hTH hp e

/-- Original nonsolvability excludes the binary field in either orientation. -/
theorem original_g2_parameter : 2 < Nat.card F := by
  cases short
  · apply d.g2_extension_parameter h hTH hp F 1 e.right e.right_injective
    rw [d.original_local_eq_residual h hTH hp 1]
    exact e.right_residual
  · apply d.g2_extension_parameter h hTH hp F 0 e.left e.left_injective
    rw [d.original_local_eq_residual h hTH hp 0]
    exact e.left_residual

/-- The faithful left source factor forces the long-first orientation. -/
theorem original_g2_orientation : short = false := by
  cases short
  · rfl
  · apply False.elim
    apply Preparation.not_g2_short_extension_left h F
      (d.original_g2_parameter h hTH hp F true e) e.left e.left_injective
    have he := d.original_local_eq_residual h hTH hp 0
    change L.subgroupOf (ChapterF.Source.parabolic ![L,R] (sourceS L H) 0) = _ at he
    rw [he]
    exact e.left_residual

/-- The original S is contained in the SAME selected right factor. -/
theorem sourceS_le_right_of_original_g2 : sourceS L H ≤ R := by
  have hor := d.original_g2_orientation h hTH hp F short e
  subst short
  apply d.sourceS_le_right_of_g2_extension h hTH F
    (d.original_g2_parameter h hTH hp F false e) e.right e.right_injective
  have he := d.original_local_eq_residual h hTH hp 1
  change R.subgroupOf (ChapterF.Source.parabolic ![L,R] (sourceS L H) 1) = _ at he
  rw [he]
  exact e.right_residual

/-- The same broad extension marking supplies the actual original core equality. -/
theorem original_g2_right_core : (R ⊔ sourceS L H).pCoreIn 2 = R.pCoreIn 2 := by
  rw [sup_eq_left.mpr (d.sourceS_le_right_of_original_g2 h hTH hp F short e)]

/-- Both whole endpoints become inner using agreement on the full overlap. -/
theorem original_g2_endpoints_inner :
    e.left.range ≤ MulAut.innerSubgroup (Model F) ∧
    e.right.range ≤ MulAut.innerSubgroup (Model F) :=
  d.original_extension_endpoints_inner h hTH hp e
    (d.sourceS_le_right_of_original_g2 h hTH hp F short e)

/-- Restrict all three original maps through the same faithful inner embedding. -/
def originalG2Comparison : RankTwoAmalgam.Iso
    (sourceParabolicAmalgam ![L,R] (sourceS L H))
      (OriginalG2.orientedAmalgam F short) :=
  (e.restrict (conj_injective_of_center_eq_bot
    (model_center_eq_bot (d.original_g2_parameter h hTH hp F short e)))
    (d.original_g2_endpoints_inner h hTH hp F short e)).trans
      (OriginalG2.intersectionIso F short)

/-- The concrete catalogue entry follows from the broad original G₂ marking. -/
theorem concreteComparison_of_original_g2 :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) := by
  apply ConcreteAmalgamComparison.g2 F
  have he := d.originalG2Comparison h hTH hp F short e
  cases short
  · exact Or.inr ⟨he.trans (ChapterF.GreenBook.LieModels.G2.borelIso.symm.reverse)⟩
  · exact Or.inl ⟨he.trans ChapterF.GreenBook.LieModels.G2.borelIso.symm⟩

/-- The original quotient fixes the field; both actual source factors contain S. -/
theorem original_g2_field_and_sylows :
    Nat.card F = 2^n ∧ (∀ i : Fin 2, sourceS L H ≤ ![L,R] i) := by
  have hor := d.original_g2_orientation h hTH hp F short e
  subst short
  have he := (d.originalG2Comparison h hTH hp F false e).trans
    (ChapterF.GreenBook.LieModels.G2.borelIso.symm.reverse)
  have hh := d.g2_local_structure h hTH hp F (Or.inr ⟨he⟩)
  exact ⟨hh.1,hh.2.2.2.2⟩

theorem originalG2Comparison_left_apply
    (x : ChapterF.Source.parabolic ![L,R] (sourceS L H) 0) :
    MulAut.conj ((d.originalG2Comparison h hTH hp F short e).left x).val = e.left x :=
  e.restrict_left_apply _ _ x

theorem originalG2Comparison_right_apply
    (x : ChapterF.Source.parabolic ![L,R] (sourceS L H) 1) :
    MulAut.conj ((d.originalG2Comparison h hTH hp F short e).right x).val = e.right x :=
  e.restrict_right_apply _ _ x

theorem originalG2Comparison_middle_apply
    (x : (ChapterF.Source.parabolic ![L,R] (sourceS L H) 0 ⊓
      ChapterF.Source.parabolic ![L,R] (sourceS L H) 1 : Subgroup G)) :
    MulAut.conj ((d.originalG2Comparison h hTH hp F short e).middle x).val =
      e.left ((sourceParabolicAmalgam ![L,R] (sourceS L H)).left x) :=
  e.restrict_middle_apply _ _ x
end Preparation
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
