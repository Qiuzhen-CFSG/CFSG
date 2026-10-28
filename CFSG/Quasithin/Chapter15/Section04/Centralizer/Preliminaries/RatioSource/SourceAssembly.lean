module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource.MinimalParabolicSource
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.SourceAssembly

/-!
# All four clauses of source 15.4.2

The source ratio proof first establishes (4) using only (1),(2) and genuine
earlier universal results. Its actual Xi-minus application then proves (3).
This supplies both original interfaces to the maximal-prime and Theorem E
assemblies, with no additional ratio or Xi-minus premise.

The universal A/C, D.1.4–5, B.6.8(5), solvable E.2.9, and 3.1.1 inputs remain
explicit in the original interface. The final source variant discharges
B.6.8(5) through its proved intrinsic Sylow theorem. The other earlier inputs
remain with their source producers; this does not assert the full Theorem E.

Source: Aschbacher–Smith, 15.4.2, printed pp.1155–1156, together with the
E-specific application of 3.2.13, printed pp.584–585.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section04.RatioSource
open MaximalPrimeSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The complete 15.4.2 source family, retaining only its genuine earlier
universal source inputs. Part (4) is constructed before the Xi-minus consumer. -/
theorem source_lemma_15_4_2
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h311 : Earlier311 (G := G))
    (hD15 : InsideCore.EarlierD15.{u}) (hD14 : InsideCore.EarlierD14Sylow.{u})
    (h685 : OutsideWitness.EarlierB685.{u})
    (h29 : OutsideWitness.EarlierE29Solvable.{u}) :
    Earlier1542 (G := G) ∧ MaximalPrimeFive.Earlier1542Four (G := G) := by
  have h44 := source_earlier1542Four hA hC h311 hD15 hD14 h685 h29
  exact ⟨InitialSource.XiMinus.source_earlier1542 hA hC h44, h44⟩

/-- The full source family with B.6.8(5) discharged. Only universal A/C,
3.1.1, the D.1.4–5 implications, and solvable E.2.9 remain explicit. -/
theorem source_lemma_15_4_2_of_D1_E2
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h311 : Earlier311 (G := G))
    (hD15 : InsideCore.EarlierD15.{u}) (hD14 : InsideCore.EarlierD14Sylow.{u})
    (h29 : OutsideWitness.EarlierE29Solvable.{u}) :
    Earlier1542 (G := G) ∧ MaximalPrimeFive.Earlier1542Four (G := G) :=
  source_lemma_15_4_2 hA hC h311 hD15 hD14 source_earlierB685 h29

end CFSG.Quasithin.Chapter15.Section04.RatioSource
