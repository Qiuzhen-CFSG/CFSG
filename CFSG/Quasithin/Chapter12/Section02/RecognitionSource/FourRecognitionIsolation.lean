module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FourRecognitionMarking
public import Theory.GroupTheory.Recognition.TransvectionFive.CoreFusionIsolation

/-!
# Dimension-four recognition reduced to isolated-root normality

The marked root-orbit and rectangle-fusion arguments now prove all the
local alternatives preceding Aschbacher 39.9. The actual marking comparison,
Held exclusion, and both uniqueness implications are already proved. Thus
source 39.9's implication from the literal isolated-root class intersection
to ambient root normality is the sole remaining input in this reduction.
Simplicity eliminates that normal root and the original configuration's
block supplies the Alternatives12213 branch.

The source 39.9 proof remains with `qt-d-12213-four-recognition`; the
normality premise below is explicit and is not claimed as established.
Source: Aschbacher, *Sporadic Groups* (1994), 39.9–41.6, pp.216–222;
Aschbacher–Smith, 12.2.27(1), p.807.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- All local input except source 39.9's ambient normality is discharged. -/
theorem four_recognition_of_isolation_normality {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (C : SplitLinearConfiguration L V 4) (hnone : NoEscape L V)
    (normality : ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.CoreFusion.RowIsolation F → F.row.Normal) :
    ClassicalGroup.IsPSL G 5 2 ∨ Nonempty (G ≃* Sporadic.Mathieu.M24) := by
  apply four_recognition_of_fusion h D C hnone
  intro hs z F hcore
  exact TransvectionFive.CoreFusion.alternatives_of_isolation_normality F hs hcore normality

/-- Both original consumers retain the actual split configuration and its block. -/
theorem four_consumers_of_isolation_normality {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (C : SplitLinearConfiguration L V 4) (hnone : NoEscape L V)
    (normality : ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.CoreFusion.RowIsolation F → F.row.Normal) :
    RecognizedGroup G 4 ∧ Alternatives12213 T L V := by
  have hr := four_recognition_of_isolation_normality h D C hnone normality
  exact ⟨recognized_four_of_classical_or_mathieu hr,
    alternatives_four_of_classical_or_mathieu C hr⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
