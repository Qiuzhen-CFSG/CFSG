module
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremC
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.ComponentInputs

/-!
# The genuine Chapter A inputs to 15.4.2(1--3)

The full source Theorem C list supplies outer solvability and even order for
the actual simple SQTK component quotients. Theorem A then supplies their
section inheritance. This discharges the model predicate in the checked
component-generation and unique-containment application to 15.4.2(1--3).
The universal A and C theorems and the exact 3.2.13 inclusion remain explicit;
the separate fourth assertion of 15.4.2 belongs to the subsequent source step.

Source: Aschbacher--Smith, 15.4.2, printed pp.1155--1156.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.TheoremCInputs
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G]
variable
  (hA : ∀ (X : Type u) [Group X] [Finite X],
    ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
  (hC : ∀ (X : Type u) [Group X] [Finite X],
    ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)

include hA hC in
/-- The original 15.4.2(1--3) conclusion with the full model predicate proved. -/
theorem source_earlier1542Conclusion
    (T : Sylow 2 G) (h : SourceHypotheses T)
    (h3213 : Chapter1.XiStarF G (T : Subgroup G) ⊆ Chapter3.XiMinus G (T : Subgroup G)) :
    Earlier1542Conclusion T :=
  ComponentInputs.source_earlier1542Conclusion hA
    (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC hC) T h h3213

include hA hC in
/-- Supply the actual universal earlier-source input of the maximal-prime proof. -/
theorem source_earlier1542
    (h3213 : ∀ T : Sylow 2 G, SourceHypotheses T →
      Chapter1.XiStarF G (T : Subgroup G) ⊆ Chapter3.XiMinus G (T : Subgroup G)) :
    Earlier1542 (G := G) :=
  ComponentInputs.source_earlier1542 hA
    (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC hC) h3213

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.TheoremCInputs
