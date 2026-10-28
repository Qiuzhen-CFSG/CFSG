module
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.SourceExclusion
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceOrbits
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.Quasithin.Rank

/-!
# The original Chapter 1 inputs in the E.6.25 construction

The actual SQTK two-core quotient satisfies the same odd-rank bounds.
The proved A.3.8 orbit bound gives a normal or index-two component
normalizer, so the two-residual normalizes every original C-component.
The completed Theorems A and C supply A.3.12 unique containment, and the
literal quotient-lifting theorem yields 1.2.4 for the original local family.

Source: Aschbacher–Smith, 1.2.1(3), 1.2.4 and E.6.25,
printed pp.504–505 and256.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
open LocalFactors
universe u

private theorem sqtk_twoCore_quotient {J : Type u} [Group J] [Finite J]
    {K : GroupClass.{u}} (hJ : IsSQTK K J) : IsSQTK K (J ⧸ pCore 2 J) := by
  refine ⟨?_,hJ.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 J) pCore_isPGroup).trans
    (hJ.stronglyQuasithin p hp ho)

/-- The original two-residual normalizes every actual local C-component. -/
theorem source_residualNormalization (K : GroupClass.{u}) : EarlierResidualNormalization K := by
  intro J _ _ hJ B hB
  rcases Chapter1.Section02.proposition_1_2_1_three_orbit_source
      (sqtk_twoCore_quotient hJ) hB with hn | hi
  · let := hn
    rw [normalizer_eq_top]
    exact le_top
  · let N := normalizer (B : Set J)
    let : N.Normal := normal_of_index_eq_two hi
    exact (pResidual_le_iff_isPGroup_quotient 2 N).mpr
      (IsPGroup.of_card (n := 1) (by rw [pow_one, ← N.index_eq_card]; exact hi))

/-- Full KnownSimple A/C supplies the original unique-containing-component input. -/
theorem source_localContainment : EarlierLocalContainment KnownSimple.IsKnownSimple.{u} := by
  intro J _ _ hJ S B hB
  exact Chapter1.Section02.lemma_1_2_4_containment_of_A_3_12
    (Chapter1.Section02.containment_of_theoremsAC
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)))
    (sqtk_twoCore_quotient hJ) S hB

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
