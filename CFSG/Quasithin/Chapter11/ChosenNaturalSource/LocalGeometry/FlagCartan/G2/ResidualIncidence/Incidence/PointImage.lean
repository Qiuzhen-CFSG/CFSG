module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.ResidualIncidence.Marked
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.SourceDisplacement

/-!
# The original G₂ point residual contains the marked Sylow image

Every member of the marked model Sylow is a conjugate, by the common flag
alignment, of a positive-root element. The standard point residual contains
that positive-root group. Surjectivity of the original local projection
therefore lifts it to L1, and the projection formula proves equality under
the literal original derived map. This discharges the image premise in the
corrected displacement-family normalizer argument.

Source: Aschbacher--Smith, opening §11.1 and 11.1.4, pp.760--761,765.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2.ResidualIncidence
open Atlas.G2 Atlas.G2.Natural Atlas.G2.Natural.OrthogonalCover
open Atlas.G2.Natural.OrthogonalCover.SylowFlag Atlas.G2.LieParabolicSetup
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))

/-- The actual point residual maps over the full marked model Sylow. -/
theorem pointMap_image_contains_sylow :
    (modelSylow S m : Subgroup _) ≤ (pointMap S m).range := by
  intro x hx
  rw [alignment_sylow S m] at hx
  obtain ⟨y,hy,rfl⟩ := hx
  have hy' : y.val ∈ standardLocal S.field.Carrier 0 :=
    (show unipotent ≤ local₂ (F := S.field.Carrier) from le_sup_left) hy
  obtain ⟨l,hl⟩ := localProjection_surjective S m 0 ⟨y.val,hy'⟩
  refine ⟨l,?_⟩
  apply Subtype.ext
  have he := congrArg Subtype.val hl
  rw [localProjection_coe] at he
  change (coordinates S m).quotientMap
    ⟨l.val,(localResidual_le _ l.property).1⟩ =
      (alignment S m).val * y.val * (alignment S m).val⁻¹
  calc
    _ = (alignment S m).val *
        ((alignment S m).val⁻¹ * (show Model S.field.Carrier from
          (coordinates S m).quotientMap ⟨l.val,(localResidual_le _ l.property).1⟩) *
          (alignment S m).val) *
          (alignment S m).val⁻¹ := by group
    _ = _ := by rw [he]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2.ResidualIncidence
