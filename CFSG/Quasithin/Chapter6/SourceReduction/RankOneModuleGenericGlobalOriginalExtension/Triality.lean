module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.Marked
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.TrialityCore
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionCatalogue

/-!
# Removing the original triality extension

The input embeds both original endpoints in the automorphism group of the
same genuine triality carrier, marking their residuals, their intersections
with the inner group, and the entire overlap. It allows outer automorphisms
and does not assume a pure comparison or a core equality.

The native quotient/core transport gives S ≤ R from the original normalized
right Borel. Full-overlap agreement and source generation make both endpoints
inner. Restricting the same three maps gives both inclusion squares to the
native triality amalgam, in either orientation. The original faithful left
factor then forces the central-first orientation, and its quotient fixes the
field exponent to n > 1. Every preparation and perfect selected R is covered;
there is no assumption that R is the whole residual of H or that S = T.

Construction of the broad marked alternatives remains with the independent
DGS source assembly. The other extension rows and final GlobalExit are not
asserted here. The literal Chapter 12 consumer uses this comparison alongside
the original linear row and rejects binary quotient types directly.

Source: Aschbacher--Smith F.1.12, pp.263--264, and 5.2.6, pp.650--651
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
namespace OriginalTriality

/-- Exchange the two distinct triality nodes. -/
@[expose] def other : Node → Node
  | .arms => .central
  | .central => .arms

variable (m : ℕ) (hm : 0 < m) (a : Node)

/-- The native root-parabolic amalgam in the literal supplied orientation. -/
@[expose] def orientedAmalgam :
    RankTwoAmalgam (parabolic (binaryParameters m hm) a)
      (borel (binaryParameters m hm)) (parabolic (binaryParameters m hm) (other a)) :=
  RankTwoAmalgam.ofSubgroups _ _ _ (borel_le_parabolic _ a) (borel_le_parabolic _ (other a))

variable {G : Type*} [Group G] (L R S : Subgroup G)

/-- Broad original triality markings retain outer parts in both endpoints.
The native local factors and full inner parabolics are marked separately. -/
abbrev Marking :=
  OriginalExtension.Marking L R S
    (localFactor (binaryParameters m hm) a) (localFactor (binaryParameters m hm) (other a))
    (parabolic (binaryParameters m hm) a) (parabolic (binaryParameters m hm) (other a))

variable {L R S}

/-- Identify the full intersection with the native Borel, keeping both squares. -/
private def intersectionIso :
    RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic (binaryParameters m hm) a)
        (parabolic (binaryParameters m hm) a ⊓ parabolic (binaryParameters m hm) (other a))
        (parabolic (binaryParameters m hm) (other a)) inf_le_left inf_le_right)
      (orientedAmalgam m hm a) := by
  have he : parabolic (binaryParameters m hm) a ⊓
      parabolic (binaryParameters m hm) (other a) = borel (binaryParameters m hm) := by
    cases a
    · exact ChapterF.GreenBook.LieModels.Triality.overlap _ rfl
    · rw [inf_comm]
      exact ChapterF.GreenBook.LieModels.Triality.overlap _ rfl
  exact { left := MulEquiv.refl _
          right := MulEquiv.refl _
          middle := MulEquiv.subgroupCongr he
          left_commutes := fun _ => Subtype.ext rfl
          right_commutes := fun _ => Subtype.ext rfl }
end OriginalTriality

namespace Preparation
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (m : ℕ) (hm : 0 < m) (a : Node)
  (e : OriginalTriality.Marking m hm a L R (sourceS L H))
include d h hTH hp e

/-- The native core calculation and normalized original Borel place S in R. -/
theorem sourceS_le_right_of_original_triality : sourceS L H ≤ R := by
  apply d.sourceS_le_right_of_triality_extension h hTH m hm (OriginalTriality.other a)
    e.right e.right_injective
  have he := d.original_local_eq_residual h hTH hp 1
  change R.subgroupOf (ChapterF.Source.parabolic ![L,R] (sourceS L H) 1) = _ at he
  rw [he]
  exact e.right_residual

/-- Both whole original triality endpoints lie in the same inner carrier. -/
theorem original_triality_endpoints_inner :
    e.left.range ≤ MulAut.innerSubgroup (BinaryCarrier m hm) ∧
    e.right.range ≤ MulAut.innerSubgroup (BinaryCarrier m hm) :=
  d.original_extension_endpoints_inner h hTH hp e
    (d.sourceS_le_right_of_original_triality h hTH hp m hm a e)

/-- Construct the pure triality comparison by restricting the original maps.
No pure comparison, inner-action premise, or core identity is assumed. -/
def originalTrialityComparison :
    RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
      (OriginalTriality.orientedAmalgam m hm a) :=
  (e.restrict
    (Theory.GroupTheory.conj_injective_of_center_eq_bot (binaryCarrier_center_eq_bot m hm))
    (d.original_triality_endpoints_inner h hTH hp m hm a e)).trans
      (OriginalTriality.intersectionIso m hm a)

/-- The actual catalogue entry from a broad marked original triality extension. -/
theorem concreteComparison_of_original_triality :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) := by
  apply ConcreteAmalgamComparison.triality m hm
  have he := d.originalTrialityComparison h hTH hp m hm a e
  cases a
  · exact Or.inl ⟨he⟩
  · exact Or.inr ⟨he⟩

/-- The original faithful left factor excludes the arms-first orientation. -/
theorem original_triality_orientation : a = .central := by
  cases a
  · exact False.elim (d.not_triality_arms_left_amalgam h hTH hp _ rfl
      ⟨d.originalTrialityComparison h hTH hp m hm .arms e⟩)
  · rfl

/-- The field exponent is the original n > 1, after the broad extension collapses. -/
theorem original_triality_field : m = n ∧ 1 < m := by
  have ha := d.original_triality_orientation h hTH hp m hm a e
  subst a
  exact (d.triality_local_structure h hTH hp m hm
    (d.originalTrialityComparison h hTH hp m hm .central e)).imp_right (fun hh => hh.1)

/-- The constructed comparison retains the original left endpoint map. -/
theorem originalTrialityComparison_left_apply
    (x : ChapterF.Source.parabolic ![L,R] (sourceS L H) 0) :
    MulAut.conj ((d.originalTrialityComparison h hTH hp m hm a e).left x).val = e.left x :=
  e.restrict_left_apply _ _ x

/-- The constructed comparison retains the original right endpoint map. -/
theorem originalTrialityComparison_right_apply
    (x : ChapterF.Source.parabolic ![L,R] (sourceS L H) 1) :
    MulAut.conj ((d.originalTrialityComparison h hTH hp m hm a e).right x).val = e.right x :=
  e.restrict_right_apply _ _ x

/-- The constructed comparison retains the entire marked Borel. -/
theorem originalTrialityComparison_middle_apply
    (x : (ChapterF.Source.parabolic ![L,R] (sourceS L H) 0 ⊓
      ChapterF.Source.parabolic ![L,R] (sourceS L H) 1 : Subgroup G)) :
    MulAut.conj ((d.originalTrialityComparison h hTH hp m hm a e).middle x).val =
      e.left ((sourceParabolicAmalgam ![L,R] (sourceS L H)).left x) :=
  e.restrict_middle_apply _ _ x
end Preparation
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
