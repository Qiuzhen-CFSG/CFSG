module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Exclusion
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Source

/-!
# Conditional assembly of the source recognition argument

Minimality preserves the actual full module after the source model selection.
The proved index and rank-kernel argument excludes every large row once its
independent fixed-space geometry is supplied. What remains is an actual SL₂(4)
quotient or the required marked natural SL₃(2) section.

`ModelBoundsAt` and `GeometryAt` remain genuine source obligations. Thus this
module does not yet prove unconditional `RecognitionAt`. The final theorem
applies the conditional recognition to the parent's literal survivor consumer;
natural corank-one exclusion remains its separate independent input.

Source: Aschbacher--Smith, 10.1.1--2 and 10.2.12, pp.741--742,754--755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Chapter3.Section02 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- Conditional source recognition; both independent source inputs must
still be proved before this discharges the published recognition obligation. -/
theorem recognition_of_model_bounds_and_geometry
    (hmodels : ModelBoundsAt T) (hgeometry : GeometryAt T) : RecognitionAt T := by
  intro L D g c
  rcases hmodels L D g c with hfour | ⟨E,hE,hrow⟩
  · exact Or.inl hfour
  · rcases hrow with hnatural | hlarge
    · exact Or.inr ⟨E,hE,hnatural⟩
    · obtain ⟨b⟩ := hlarge
      obtain ⟨_,cE⟩ := c.reselect E hE
      exact (b.false_of_configuration cE
        (hgeometry cE.many L E cE.minimal cE.nonnormal cE.notA5
          cE.pointCentralizers b.crossed b.fixed_size_gt_eight)).elim

/-- The actual parent's survivor application, with the remaining earlier
source and natural-corank premises all displayed. -/
theorem survivor_of_model_bounds_geometry_and_natural_exclusion
    (hmodels : ModelBoundsAt T) (hgeometry : GeometryAt T)
    (hexclusion : NaturalSmallCorankExclusionAt T)
    {L : Subgroup G} {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    {g : G} (c : Configuration T D g) :
    ∃ E : FundamentalSetup KnownSimple.IsKnownSimple T L,
      E.fullModule = D.fullModule ∧ Nonempty (SourceLinearThreeGeometry T E) ∧
      2 ≤ globalW E.fullModule (T : Subgroup G) :=
  c.survivor_of_source_steps (recognition_of_model_bounds_and_geometry hmodels hgeometry) hexclusion

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
