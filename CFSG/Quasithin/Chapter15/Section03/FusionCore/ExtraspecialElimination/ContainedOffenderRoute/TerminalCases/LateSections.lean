module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReductionAssembly
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.NaturalSelection.Transport

/-!
# A strong offender on the classified late section

Apply the full corrected B.5.1 implication to the late actor. The later
selected subgroup remains strong on its literal component commutator modulo
the component fixed space, since taking this section decreases fixed
codimension. Consequently this section has quadratic ratio different from
one. The complete classification witness is retained for case analysis.

This discharges the transport needed by the exceptional-row exclusions;
it does not identify a group from a numerical ratio alone.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.1.5,
pp.69–70, B.5.1, pp.99–103, and the first paragraph on p.1145.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases

open Subgroup Representation Representation.BinaryOffender
open ReducedModels ComponentReduction ModelReduction BinaryModels
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open scoped IsMulCommutative

universe u
variable {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E L upper : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (r : ReducedModels.Input κ H M Y V Y0 T ZS Z E L upper)
    (s : StrongPlacement r)

/-- The actual later subgroup is strong on the full B.5.1 moved section.
No claim about its membership in the first offender span is used. -/
theorem strong_on_late_section
    (c : MovedSection
      (r.placed.action.representation.comp (lateActor r.placed.action).subtype)
      ((starImage H L).subgroupOf (lateActor r.placed.action))) :
    IsStrongOffender c.action
      ((starImage H s.selected.carrier).subgroupOf (lateActor r.placed.action)) := by
  have hs := s.late_offender.2.2
  exact ⟨hs.1, (ReducedModels.NaturalSelection.movedSection_codim_le c _).trans_lt hs.2⟩

include s in
/-- An actual strong offender excludes ratio one on this same section. -/
theorem late_section_ratio_ne_one
    (c : MovedSection
      (r.placed.action.representation.comp (lateActor r.placed.action).subtype)
      ((starImage H L).subgroupOf (lateActor r.placed.action))) :
    quadraticRatio c.action ≠ 1 := by
  intro hq
  have hs := strong_on_late_section r s c
  have ho : IsOffender c.action
      ((starImage H s.selected.carrier).subgroupOf (lateActor r.placed.action)) :=
    ⟨hs.1, hs.2.le⟩
  have he := (ho.best_and_codim_eq_of_quadraticRatio_eq_one c.action hq).2
  exact (Nat.ne_of_lt hs.2) he

/-- Full B.5.1 applied to the correct actor, with strong offending and the
ratio-one exclusion on its classified section. Every source clause survives. -/
theorem exists_strong_source_section
    (sections : EarlierComponentSections κ)
    (orbits : OrbitClosure.EarlierOrbitAlternative κ)
    (source : ProjectiveLine.QuasisimpleClassificationInput.{u,u} κ) :
    ∃ c : ProjectiveLine.QuasisimpleSourceConclusion
      (r.placed.action.representation.comp (lateActor r.placed.action).subtype)
      ((starImage H L).subgroupOf (lateActor r.placed.action)),
      IsStrongOffender c.sectionData.action
        ((starImage H s.selected.carrier).subgroupOf (lateActor r.placed.action)) ∧
        quadraticRatio c.sectionData.action ≠ 1 := by
  obtain ⟨c⟩ := r.late_source_conclusion sections orbits source
  exact ⟨c, strong_on_late_section r s c.sectionData,
    late_section_ratio_ne_one r s c.sectionData⟩

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases
