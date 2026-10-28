module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.SmallModules.SixQuotient
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.SmallModules.SixCovers

/-!
# Excluding the terminal alternating-six component

The full corrected B.5.1 conclusion selects the marked six-letter natural
action on the literal component-commutator quotient. Strong offending removes
the alternating-only actor, leaving the symmetric actor with its actual A₆
component. Perfect-central-cover recognition then recovers either the natural
module or the augmentation core, equivariantly for that same actor marking.

The classified moved space equals the terminal point space. Its proper point
stabilizer contains the later strong offender in its intrinsic two-core, so
the six-letter point calculation excludes both recovered modules. No module
coordinates, actor equality, or point-core bound is an additional premise.

Only the earlier component-section and orbit implications and full corrected
B.5.1 implication remain source parameters, as in the binary branch. Their
discharge and the degree-four/five branches belong to the original terminal
source assembly, not to this conditional small-module reduction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.3.2–3,
printed pp.83–84; B.4.2, p.86; B.5.1, pp.99–103; and 15.3.49, p.1145.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.SmallModules
open ReducedModels ComponentReduction ModelReduction BinaryModels ModelExclusions

universe u v

/-- Select the actual quotient coordinates from full B.5.1, and discharge
the central-cover recognition hypotheses on that same moved section. Both
natural and core possibilities survive, with the compatible S₆ marking. -/
theorem six_case_of_source {D : Type u} [Group D] [Finite D]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} {J : Subgroup D} {κ : GroupClass.{u}}
    (h : QuasisimpleSourceHypothesis ρ κ J)
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ J)
    (e : J ≃* alternatingGroup (Fin 6)) (hs : IsStrongFFModule ρ) :
    PointCases.SixModuleCase c.sectionData.space.toRepresentation J := by
  let := h.finite_module
  obtain ⟨hi, a, ha⟩ := six_quotient_of_source h c e hs
  exact SixCovers.moved_symmetric ρ J c.sectionData hi a ha

variable {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E L upper : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    {r : ReducedModels.Input κ H M Y V Y0 T ZS Z E L upper}

/-- Construct the six-letter module case on the literal terminal point
space from an actual A₆ component equivalence and universal source inputs. -/
theorem six_on_point (p : TerminalPoint r) (s : StrongPlacement r)
    (sections : EarlierComponentSections κ)
    (orbits : OrbitClosure.EarlierOrbitAlternative κ)
    (source : ProjectiveLine.QuasisimpleClassificationInput.{u,u} κ)
    (e : starImage H L ≃* alternatingGroup (Fin 6)) :
    PointCases.SixModuleCase (PointOnLateActor.space p).toRepresentation
      ((starImage H L).subgroupOf (lateActor r.placed.action)) := by
  obtain ⟨c⟩ := r.late_source_conclusion sections orbits source
  have h := six_case_of_source (r.late_source_hypothesis sections orbits) c
    ((subgroupOfEquivOfLe (r.component_le_late_actor sections orbits)).trans e)
    ⟨_, s.late_offender.2.2⟩
  rw [point_space_eq p sections orbits c.sectionData]
  exact h

/-- The original A₆ component branch contradicts the later strong offender
in the intrinsic two-core of the actual restricted point stabilizer. -/
theorem exclude_six (p : TerminalPoint r) (s : StrongPlacement r)
    (sections : EarlierComponentSections κ)
    (orbits : OrbitClosure.EarlierOrbitAlternative κ)
    (source : ProjectiveLine.QuasisimpleClassificationInput.{u,u} κ)
    (e : starImage H L ≃* alternatingGroup (Fin 6)) : False :=
  PointOnLateActor.exclude_six p s sections orbits
    (six_on_point p s sections orbits source e)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.SmallModules
