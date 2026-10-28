module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.AmbientGeometry.LiteralNormalizer.Reduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.Normalizer.ActionRealization

/-!
# The literal core action is realized in max1

The actual ambient embedding identifies the two-core of certified max1 with
the mapped local kernel. The model theorem realizes every normalizer action
on every element of this kernel. Applying it to the eleven literal basis
words gives the action-realization input for the chapter's normalizer assembly.

Source: GLS3, Table 5.3i, printed p.270; the literal ATLAS max1 words and
their provenance are documented in `Janko4.Model.Cardinality.Subgroup`.
-/

public section

open Subgroup Janko4 Janko4.Cardinality
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.AmbientGeometry

/-- Every ambient normalizer element has the same action on the eleven literal
core generators as an element of the certified Mathieu subgroup. -/
theorem literalCoreActionRealization : LiteralCoreActionRealization := by
  intro g hg
  rw [literalCore_eq_embedded_localKernel] at hg
  obtain ⟨h, hh, he⟩ := LocalStructure.MathieuNormalizer.localKernel_action_realization g hg
  refine ⟨h, hh, fun i => he _ ?_⟩
  rw [← literalCore_eq_embedded_localKernel]
  exact literalCoreGenerator_mem i

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.AmbientGeometry
