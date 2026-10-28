module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FourRecognitionFusion
public import Theory.GroupTheory.Recognition.TransvectionFive.CoreFusionSeparation

/-!
# Dimension-four recognition after mixed-core separation

The mixed core orbit is excluded from point fusion by its characteristic
second derived line. This discharges source 39.4 inside the original
12.2.27(1) consumer. The remaining source 39.10 input consists only of
fusion of the two root representatives; both it and the final assembly
remain with `qt-d-12213-four-recognition`.

Source: Aschbacher, *Sporadic Groups* (1994), 39.4–39.10, pp.214–216;
Aschbacher–Smith 12.2.27(1), p.807.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open TransvectionFive.UniquenessLinear.PlaneTensor
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The core-exclusion premise is proved; only the two positive root-fusion
assertions of source 39.10 remain with this same assembly owner. -/
theorem four_recognition_of_root_orbits {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (C : SplitLinearConfiguration L V 4) (hnone : NoEscape L V)
    (rootOrbits : IsSimpleGroup G → ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z →
        IsConj z (element F 1) ∧ IsConj z (element F 32)) :
    ClassicalGroup.IsPSL G 5 2 ∨ Nonempty (G ≃* Sporadic.Mathieu.M24) := by
  apply four_recognition_of_core_orbits h D C hnone
  intro hs z F hcore
  exact ⟨(rootOrbits hs z F hcore).1,(rootOrbits hs z F hcore).2,
    TransvectionFive.CoreFusion.not_conjugate_core33 F⟩

/-- Both original consumers use the literal block of the original split
configuration after the proved mixed-core exclusion. -/
theorem four_consumers_of_root_orbits {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (C : SplitLinearConfiguration L V 4) (hnone : NoEscape L V)
    (rootOrbits : IsSimpleGroup G → ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z →
        IsConj z (element F 1) ∧ IsConj z (element F 32)) :
    RecognizedGroup G 4 ∧ Alternatives12213 T L V := by
  have hr := four_recognition_of_root_orbits h D C hnone rootOrbits
  exact ⟨recognized_four_of_classical_or_mathieu hr,
    alternatives_four_of_classical_or_mathieu C hr⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
