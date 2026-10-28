module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FourRecognitionMarking
public import Theory.GroupTheory.Recognition.TransvectionFive.FusionTypes

/-!
# Dimension-four recognition reduced to source core fusion

The marked affine comparison and the two uniqueness implications are proved.
The new rectangle census and root-normalizer argument reduce the remaining
fusion-alternatives input to three actual core representatives in each of the
two opposite markings: the row root, column root and non-root involution.
These are consequences of Aschbacher 39.10(1). Their construction from
simplicity and point-core fusion remains with this same final assembly owner,
`qt-d-12213-four-recognition`. Thus this is a conditional reduction, not an
unconditional proof of 12.2.27(1).

Source: Aschbacher–Smith 12.2.27(1), p.807; Aschbacher, *Sporadic Groups*
(1994), 39.10 and 40.2–41.6, pp.216–222.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open TransvectionFive.UniquenessLinear
open TransvectionFive.UniquenessLinear.PlaneTensor
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- Three literal core representatives suffice at each end of the flag.
The remaining input is the source 39.10 calculation, not recognition. -/
theorem four_recognition_of_core_orbits {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (C : SplitLinearConfiguration L V 4) (hnone : NoEscape L V)
    (coreOrbits : IsSimpleGroup G → ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z →
        IsConj z (element F 1) ∧ IsConj z (element F 32) ∧ ¬ IsConj z (element F 33)) :
    ClassicalGroup.IsPSL G 5 2 ∨ Nonempty (G ≃* Sporadic.Mathieu.M24) := by
  apply four_recognition_of_fusion h D C hnone
  intro hs z F hcore
  obtain ⟨h1,h32,h33⟩ := coreOrbits hs z F hcore
  obtain ⟨h1',h32',h33'⟩ := coreOrbits hs z (oppositeMarking F) hcore
  exact TransvectionFive.FusionTypes.alternatives_of_tests F h1 h32 h33 h1' h32' h33'

/-- The same reduction reaches both original dimension-four consumer types,
using the literal block from the original split configuration. -/
theorem four_consumers_of_core_orbits {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (C : SplitLinearConfiguration L V 4) (hnone : NoEscape L V)
    (coreOrbits : IsSimpleGroup G → ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z →
        IsConj z (element F 1) ∧ IsConj z (element F 32) ∧ ¬ IsConj z (element F 33)) :
    RecognizedGroup G 4 ∧ Alternatives12213 T L V := by
  have hr := four_recognition_of_core_orbits h D C hnone coreOrbits
  exact ⟨recognized_four_of_classical_or_mathieu hr,
    alternatives_four_of_classical_or_mathieu C hr⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
