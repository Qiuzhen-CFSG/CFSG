module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.QuotientStructure
public import CFSG.Quasithin.ChapterA.Section01.SectionRank.CyclicCentralizers

/-!
# A.1.31(1) on the literal M/O₂(M) quotient

The source theorem closes the universal A.1.31 input of the quotient
calculation in 15.4.12. Its specialization below uses exactly CoreQuotient M
and keeps the prime-rank hypothesis on M. The other earlier-source inputs
and local witnesses remain with the family construction owner.

Source: Aschbacher–Smith, A.1.31(1), pp.27–28, and 15.4.12, pp.1160–1161.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.QuotientStructure
universe u

/-- The complete, proved first clause of A.1.31. -/
theorem a131One : A131One.{u} := by
  intro H _ _ p _ N _ hrank hp hF R hR hne
  exact CFSG.Quasithin.ChapterA.lemma_A_1_31_1 hrank hp hF R hR hne

/-- The cyclic-centralizer conclusion on the fixed quotient M/O₂(M), with
no universal A.1.31 assumption. -/
theorem coreQuotient_centralizer_cyclic
    {G : Type u} [Group G] [Finite G] (M : Subgroup G)
    {p : ℕ} [Fact p.Prime] (hrank : primeRank p M ≤ 2) (hp : Odd p)
    (hF : Theory.GroupTheory.generalizedFitting (CoreQuotient M) = pCore p (CoreQuotient M))
    (R : Subgroup (CoreQuotient M)) (hR : IsPGroup 2 R) (hne : R ≠ ⊥) :
    IsCyclic (pCore p (CoreQuotient M) ⊓ centralizer (R : Set (CoreQuotient M)) :
      Subgroup (CoreQuotient M)) :=
  a131One (N := pCore 2 M) hrank hp hF R hR hne

end CFSG.Quasithin.Chapter15.Section04.FamilySource.QuotientStructure
