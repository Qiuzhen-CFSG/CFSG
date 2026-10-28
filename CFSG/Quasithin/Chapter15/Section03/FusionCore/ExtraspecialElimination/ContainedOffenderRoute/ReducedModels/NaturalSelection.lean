module
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.NaturalSelection.Transport
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.NaturalSelection.FivePoint
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.NaturalSelection.Local

/-!
# Selecting the natural component section and excluding larger fields

Apply the full corrected B.5.1 conclusion to the genuine late actor. Its
component is SL₂, so the component order-four comparison leaves the natural
row and the S₅ row above A₅. In the latter row the actual contained best
offender remains quadratic and best on the central quotient. The ratio-one
argument also preserves offender generation. The resulting S₅ marking carries
the local subgroup to a Sylow overgroup with a cubic element. Its two-core
lies in A₅, contradicting the commuting-transposition offender clause.

The surviving natural action is transported to the literal component section
inside U_H/Z, including the fixed-space quotient and the selected defining
field. Its model need not equal the supplied model. The field-exclusion
consumer supplies containment and uses the existing compatible Borel marking
and splitting theorem. Only the universal earlier appendix implications and
the two seed conditions from 15.3.48(2) remain as inputs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2 p.86,
B.5.1 pp.99–103, and the proof of 15.3.49 on printed p.1144.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels
universe u
namespace Input
variable {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E L upper : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : Input κ H M Y V Y0 T ZS Z E L upper)
include d

/-- The actual contained offender remains quadratic and best on the
ratio-one central quotient, and remains in the correct relative local core. -/
theorem late_selected_on_section
    (s : MovedSection (d.placed.action.representation.comp (lateActor d.placed.action).subtype)
      ((starImage H L).subgroupOf (lateActor d.placed.action)))
    (hq : quadraticRatio s.action = 1) :
    let A := (starImage H d.placed.selected.carrier).subgroupOf (lateActor d.placed.action)
    IsBestOffender s.action A ∧ IsQuadratic s.action A ∧ A ≤ d.lateLocal.pCoreIn 2 := by
  obtain ⟨_, hb, hquad, hcore⟩ := d.late_selected_offender
  exact ⟨NaturalSelection.best_on_movedSection s hq hb,
    NaturalSelection.quadratic_on_movedSection _ s hquad,
    (comap_mono hcore).trans (NaturalSelection.core_restrict _ _)⟩

/-- The full corrected B.5.1 list selects natural coordinates on the
original component section. The intrinsic S₅ core calculation excludes
the remaining nonnatural row using the actual contained offender. -/
theorem natural_component_section
    (sections : EarlierComponentSections κ)
    (orbits : BinaryModels.OrbitClosure.EarlierOrbitAlternative κ)
    (source : ProjectiveLine.QuasisimpleClassificationInput.{u,u} κ)
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (e : starImage H (localSpan L T) ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    Nonempty (Representation.SL2CubicFixedSection.NaturalComponentSection
      (F := F) d.placed.action.representation (starImage H (localSpan L T))
      (LargerFields.componentSection Z H ZS L T)) := by
  have hclosed := (d.structure_of_earlier sections orbits).1
  let P := lateActor d.placed.action
  let J := (starImage H L).subgroupOf P
  have hLP := d.component_le_late_actor sections orbits
  let eL : starImage H L ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (MulEquiv.subgroupCongr (by rw [hclosed])).trans e
  let eJ : J ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (subgroupOfEquivOfLe hLP).trans eL
  obtain ⟨c⟩ := d.late_source_conclusion sections orbits source
  obtain ⟨B, ⟨b⟩⟩ | ⟨_, hbad⟩ := NaturalSelection.moved_natural_or_five
    (d.placed.action.representation.comp P.subtype) eJ c.sectionData c.clause_one
  · let f : B.Carrier ≃+* F :=
      LargerFields.NaturalCoordinates.fieldEquiv_of_sl2Equiv (b.groupEquiv.symm.trans eJ)
    let bf := LargerFields.NaturalCoordinates.transport_natural
      (c.sectionData.action.comp J.subtype) b f
    have hU : LargerFields.componentSection Z H ZS L T =
        moved d.placed.action.representation (starImage H L) := by
      rw [LargerFields.NaturalCoordinates.componentSection_eq_moved Z H ZS L T
        d.placed.action d.closure_le, hclosed]
    have hn := NaturalSelection.section_of_restriction hLP c.sectionData _ hU bf
    rw [hclosed]
    exact ⟨hn⟩
  · obtain ⟨mark, ho, hq⟩ := hbad
    have hgen := NaturalSelection.movedSection_generated c.sectionData hq
      (lateActor_offenderSubgroup_eq_top d.placed.action)
    obtain ⟨hA, _, hcore⟩ := d.late_selected_on_section c.sectionData hq
    obtain ⟨S, hS⟩ := d.lateLocal_contains_sylow
    exact (NaturalSelection.not_five_of_local_core hgen hA hcore S hS
      (d.lateLocal_three_dvd sections orbits) ⟨mark, ho, hq⟩).elim

/-- Actual field exclusion after the universal appendix inputs and the two
seed statements of 15.3.48(2); containment is discharged here. -/
theorem no_larger_field_of_earlier
    (sections : EarlierComponentSections κ)
    (orbits : BinaryModels.OrbitClosure.EarlierOrbitAlternative κ)
    (source : ProjectiveLine.QuasisimpleClassificationInput.{u,u} κ)
    (hB214 : CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry.SourceB214Splitting.{u})
    (hZST : ZS ≤ T) (h48 : ⁅ZS, T⁆ ≤ Z) :
    BinaryModels.ModelSieve.NoLargerField (L ⧸ pCore 2 L) := by
  exact d.no_larger_field_of_natural_sections orbits hB214 hZST h48
    (fun e _ => d.natural_component_section sections orbits source e)
    (d.y_le_closure sections)

end Input
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels
