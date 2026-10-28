module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.Inputs
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.Inputs

/-!
# The contained actor satisfies the source FF hypotheses

The action is the restriction of the given SectionAction to J*, where
J = localSpan selected.carrier H. Its SQTK cover is the actual subgroup
J inside H, with the kernel of its star projection. This packages the
proved classification hypotheses into the existing appendix interface;
the nontrivial FF witness is retained separately to exclude the trivial
actor allowed by the literal B.5.3 hypotheses.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.3,
printed p.104, and proof of 15.3.49(i), printed pp.1143–1144.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence

open ComponentReduction FactorGeneration
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison

universe u
variable {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : PlacedInput κ H M Y V Y0 T ZS Z E)

/-- The actual representation on the seed span modulo its specified line. -/
noncomputable abbrev starAction :=
  d.action.representation.comp (starImage H (localSpan d.selected.carrier H)).subtype

/-- A literal SQTK quotient presentation, with its first-isomorphism map. -/
noncomputable def starCover : SQTKQuotient κ (starImage H (localSpan d.selected.carrier H)) where
  Cover := (localSpan d.selected.carrier H).subgroupOf H
  kernel := (spanStarProjection H d.selected.carrier).ker
  sqtk := spanStarCover_sqtk H d.selected.carrier d.sqtk
  equiv := spanStarQuotientEquiv H d.selected.carrier

/-- B.5.3 is verified for the constructed contained actor, on the same action. -/
theorem starHypothesis : FFHypothesis κ (starAction d) := by
  obtain ⟨hfinite, hfaithful, hcore, hgenerated, _, _⟩ :=
    star_span_classification_hypotheses H ZS Z d.selected.carrier d.action
      d.sqtk d.selected.le_local d.selected.best
  exact ⟨hfinite, hfaithful, hcore, hgenerated, ⟨starCover d⟩⟩

/-- The selected best offender supplies the nontrivial FF witness. -/
theorem starFFWitness : IsFFModule (starAction d) :=
  star_span_isFFModule H ZS Z d.selected.carrier d.action d.selected.best

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence
