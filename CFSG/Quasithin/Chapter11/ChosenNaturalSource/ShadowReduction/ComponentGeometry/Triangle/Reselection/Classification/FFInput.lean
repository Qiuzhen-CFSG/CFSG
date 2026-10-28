module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification.Projection
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification.Supplement

/-!
# The earlier FF supplement of the literal component

The canonical component projection identifies the actual simple quotient.
Adjoining a full-normalizer offender and passing to the B.5.1 offender group
retains that projection and its original action. Complete B.5.1 then applies
on the unchanged chosen space; no model marking is assumed.

Source: Aschbacher--Smith 3.2.8 and 11.0.2, printed pp.582 and 759--760.
-/

set_option Elab.async false

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.QuasisimpleNormalizer
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- A full-normalizer offender yields the completed B.5.1 input, without
assuming the offender lies in the component or its seed actor. -/
theorem source_conclusion
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hff : IsFFModule (normalizerRepresentation D.chosenAction)) :
    ∃ A : Subgroup (linearNormalizer D.seedComponentAction),
      IsOffender (normalizerRepresentation D.seedComponentAction) A ∧
      ModuleClassification.NormalizerConclusion D.seedComponentAction A :=
  D.full_normalizer_source_conclusion h ((fullNormalizer_ff_iff D).mp hff)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification
