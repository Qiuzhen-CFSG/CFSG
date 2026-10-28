module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.OriginalCenterElementary
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.FixedFactorReduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.CoreQuotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.CoreQuotient.Displacement

/-!
# Original rank-two center control from literal quotient estimates

The exact fixed-factor reduction gives center order 32. The original
InputSetup.coreEquiv transports this and the established elementarity
to the actual commutator core. The action is induced by the original
LocalSource projection on K/Vcirc.

The elementary quotient and sharp involution fixed-index estimate remain
explicit source obligations. Q-triviality follows from elementarity. Earlier is discharged by
the independent (4.4) producer. This conditional consumer does not
complete MS93 or C.1.34.
Source: Meierfrankenfeld--Stellmacher (1993), (4.5)(iii)--(iv) and
section 7, printed pp.895--900,932--933.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
open DistanceEight.CoreFactors.Center
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}}
  {L R : Subgroup J} {h : Input κ L R} (t : InputSetup h)

/-- Exact cardinality transported through the original core isomorphism.
The elementary quotient and its sharp displacement remain source inputs. -/
theorem original_core_center_card_of_quotient_control
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    [IsElementaryAbelian 2 (CoreQuotient.Space t.reduction.radical)]
    (m : t.reduction.overgroup)
    (ht : t.source.projection m ^ 2 = 1) (hne : t.source.projection m ≠ 1)
    (hsmall : (FixedPoints.subgroup
      (zpowers (CoreQuotient.localAction t.reduction.radical m))
      (CoreQuotient.Space t.reduction.radical)).index ≤ 16) :
    Nat.card (center (commutatorCore L)) = 32 := by
  rw [← Nat.card_congr (centerCongr t.coreEquiv).toEquiv]
  exact core_center_card_of_moving_index_bound common earlier
    (CoreQuotient.moving_index_bound
      (CoreQuotient.Q_commutator_le_of_elementary common earlier) m ht hne hsmall)

/-- The original rank-two numerical consumer, with precisely the remaining
quotient-control premises rather than an assumed center bound. -/
theorem original_core_center_control_of_quotient_control
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    [IsElementaryAbelian 2 (CoreQuotient.Space t.reduction.radical)]
    (m : t.reduction.overgroup)
    (ht : t.source.projection m ^ 2 = 1) (hne : t.source.projection m ≠ 1)
    (hsmall : (FixedPoints.subgroup
      (zpowers (CoreQuotient.localAction t.reduction.radical m))
      (CoreQuotient.Space t.reduction.radical)).index ≤ 16) :
    IsElementaryAbelian 2 (center (commutatorCore L)) ∧
      Nat.card (center (commutatorCore L)) ≤ 32 :=
  ⟨t.original_core_center_elementary common earlier,
    (t.original_core_center_card_of_quotient_control common earlier m ht hne hsmall).le⟩

/-- The original cardinality consumer of the neighboring displacement estimate.
The explicit estimate includes the full error modulo Vcirc, including its
first-hat intersection. Its source construction remains an obligation. -/
theorem original_core_center_card_of_neighbor_displacement
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    [IsElementaryAbelian 2 (CoreQuotient.Space t.reduction.radical)]
    (p : DistanceEight.CoreFactors.Early.SourcePath t.reduction.radical
      (alpha t.reduction.radical))
    (m : t.reduction.overgroup)
    (ht : t.source.projection m ^ 2 = 1) (hne : t.source.projection m ≠ 1)
    (hsmall : (Vcirc t.reduction.radical (alpha t.reduction.radical)).relIndex
      (CoreQuotient.neighborDisplacement p m) ≤ 4) :
    Nat.card (center (commutatorCore L)) = 32 :=
  t.original_core_center_card_of_quotient_control common earlier m ht hne
    (CoreQuotient.fixed_index_le_sixteen_of_neighbor_displacement common earlier p m hsmall)

/-- The numerical original-source consumer, with the remaining geometric
small-error premise exposed rather than an assumed center bound. -/
theorem original_core_center_control_of_neighbor_displacement
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    [IsElementaryAbelian 2 (CoreQuotient.Space t.reduction.radical)]
    (p : DistanceEight.CoreFactors.Early.SourcePath t.reduction.radical
      (alpha t.reduction.radical))
    (m : t.reduction.overgroup)
    (ht : t.source.projection m ^ 2 = 1) (hne : t.source.projection m ≠ 1)
    (hsmall : (Vcirc t.reduction.radical (alpha t.reduction.radical)).relIndex
      (CoreQuotient.neighborDisplacement p m) ≤ 4) :
    IsElementaryAbelian 2 (center (commutatorCore L)) ∧
      Nat.card (center (commutatorCore L)) ≤ 32 :=
  ⟨t.original_core_center_elementary common earlier,
    (t.original_core_center_card_of_neighbor_displacement common earlier p m ht hne hsmall).le⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
