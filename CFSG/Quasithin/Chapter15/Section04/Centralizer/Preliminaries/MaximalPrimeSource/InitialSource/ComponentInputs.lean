module

public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Containment
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource

/-!
# Supplying the Chapter A component inputs to 15.4.2(1--3)

The proved A.3.9 generation and A.3.12 unique containment, together with the
proved noncentral A.3.6 input, discharge all three component assumptions in
the existing initial source deduction. The original simple QTKE group, full
Sylow subgroup, empty faithful family and two distinct maximal two-local
overgroups of central omega remain in `SourceHypotheses`.

The genuine universal Theorem A and the simple SQTK outer-solvability/even-order
input remain explicit, as does the exact inclusion from 3.2.13. Their earlier
source discharge and the separate fourth part of 15.4.2 belong to final assembly.

Source: Aschbacher--Smith, A.3.9(1), A.3.12 (pp.46--48), and
15.4.2(1--3) (pp.1155--1156), combined 1 March 2004 manuscript.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.ComponentInputs
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G]

variable
  (hA : ∀ (X : Type u) [Group X] [Finite X],
    ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
  (hSimple : ∀ (S : Type u) [Group S] [Finite S],
    IsSimpleGroup S → ¬ IsMulCommutative S → IsSQTK KnownSimple.IsKnownSimple S →
      Group.IsSolvable (MulAut.Outer S) ∧ Even (Nat.card S))

include hA hSimple in
/-- The actual 15.4.2(1--3) consumer with all Chapter A component premises supplied. -/
theorem source_earlier1542Conclusion
    (T : Sylow 2 G) (h : SourceHypotheses T)
    (h3213 : Chapter1.XiStarF G (T : Subgroup G) ⊆ Chapter3.XiMinus G (T : Subgroup G)) :
    Earlier1542Conclusion T :=
  InitialSource.source_earlier1542Conclusion
    (fun X _ _ hX hO S B hB => ChapterA.Section03.SourceComponents.containment (G := X)
      hA hSimple hX hO S B hB)
    (ChapterA.Section03.CComponentCommutation.noncentralStructureInput KnownSimple.IsKnownSimple)
    (fun X _ _ hX hO => ChapterA.Section03.SourceComponents.generation (G := X) hA hSimple hX hO)
    T h h3213

include hA hSimple in
/-- Supply the literal universal earlier-source input for the maximal-prime reduction. -/
theorem source_earlier1542
    (h3213 : ∀ T : Sylow 2 G, SourceHypotheses T →
      Chapter1.XiStarF G (T : Subgroup G) ⊆ Chapter3.XiMinus G (T : Subgroup G)) :
    Earlier1542 (G := G) :=
  InitialSource.source_earlier1542
    (fun X _ _ hX hO S B hB => ChapterA.Section03.SourceComponents.containment (G := X)
      hA hSimple hX hO S B hB)
    (ChapterA.Section03.CComponentCommutation.noncentralStructureInput KnownSimple.IsKnownSimple)
    (fun X _ _ hX hO => ChapterA.Section03.SourceComponents.generation (G := X) hA hSimple hX hO)
    h3213

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.ComponentInputs
