module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource.SourceAssembly
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.SourceSylow

/-!
# Discharging the D.1.4 Sylow input in source 15.4.2

The proved solvable D.1.4 alternative acts on the same conjugation image and
uses the same chief series as the inside-core source implication. Its Sylow
witness is already the required subtype image, so no replacement group or
module is introduced. The complete source 15.4.2 consumer now retains only
D.1.5 among its earlier D.1 inputs.

Source: Aschbacher--Smith, D.1.4, p.176, and 15.4.2(4), p.1156.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section04.RatioSource
universe u

/-- The entire earlier D.1.4 implication used by the ratio proof is proved. -/
theorem InsideCore.source_earlierD14Sylow : InsideCore.EarlierD14Sylow.{u} := by
  intro X _ G₁ G₂ T V d _ hV hu hs _
  obtain ⟨_,_,s,hcount⟩ := hu
  have hc : ChapterD.UniqueFactor.HasUniqueNoncentralChiefFactor G₂ V := ⟨s,hcount⟩
  exact ChapterD.UniqueFactor.source_dualFF_or_sylow d hV hc hs

variable {G : Type u} [Group G] [Finite G]
/-- All four source clauses with both B.6.8(5) and D.1.4 discharged. -/
theorem source_lemma_15_4_2_of_D15_E2
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h311 : Earlier311 (G := G))
    (hD15 : InsideCore.EarlierD15.{u})
    (h29 : OutsideWitness.EarlierE29Solvable.{u}) :
    MaximalPrimeSource.Earlier1542 (G := G) ∧
      MaximalPrimeFive.Earlier1542Four (G := G) :=
  source_lemma_15_4_2_of_D1_E2 hA hC h311 hD15 InsideCore.source_earlierD14Sylow h29

end CFSG.Quasithin.Chapter15.Section04.RatioSource
