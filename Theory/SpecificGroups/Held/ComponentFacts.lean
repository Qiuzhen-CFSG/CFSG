module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure.Application
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer
public import Theory.SpecificGroups.Held.LocalPairs.SylowPointwise
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.Planes
public import Theory.GroupAction.ElementarySylowFixerBound
public import Theory.GroupTheory.PrimeRankWitness

/-!
# Held facts for the ordinary component argument

The certified plane in Held gives three-rank at least two. The proved full
automorphism realization and permutation-normalizer bound make Out(He) a
two-group. The same realization makes every pointwise Sylow fixer inner;
the certified center of order two then bounds its elementary fixer subgroups.
No simplicity, order, or local catalogue premise is added.

Source: GLS3 Table 5.3p and the ATLAS HeG1-p2058B0 model used by the imported
certificates; Aschbacher--Smith 15.1.22(**),(5), printed pp.1099--1100.
-/

public section
namespace Held
open Subgroup Theory.GroupTheory Theory.GroupAction

/-- The concrete coordinate plane embeds an elementary nine into Held. -/
theorem three_rank_ge_two : 2 ≤ primeRank 3 He := by
  let f := LocalPairs.PairCoverage.LocalActions.RepresentativeImages.oddEmbedding false 0
  apply primeRank_ge_of_elementary_embedding (f := f) ?_ ?_
    (LocalPairs.PairCoverage.LocalActions.RepresentativeImages.oddEmbedding_injective false 0)
  · intro x
    funext i
    exact ZModModule.char_nsmul_eq_zero 3 (x.toAdd i)
  · simp [LocalPairs.PairCoverage.LocalActions.Plane, Nat.card_eq_fintype_card]

/-- The full outer group, with automorphism realization discharged. -/
theorem outer_isPGroup_two : IsPGroup 2 (MulAut.Outer He) :=
  isPGroup_outer_of_normalizer permutationGroup 2 Realization.normalizer_surjective
    isPGroup_permutationNormalizerQuotient

/-- Every elementary subgroup fixing a Held Sylow pointwise has order at most two. -/
theorem elementary_sylow_fixer_card_le_two
    (S : Sylow 2 He) (A : Subgroup (MulAut He)) [IsElementaryAbelian 2 A]
    (hfix : ∀ a ∈ A, ∀ x ∈ S, a x = x) : Nat.card A ≤ 2 := by
  let : IsCyclic (center S) :=
    isCyclic_of_prime_card (LocalPairs.SylowGeometry.Calculations.inner_center_card S)
  apply elementary_sylow_fixer_card_le_two_of_inner S LocalPairs.center_eq_bot _ A hfix
  intro a _ ha
  obtain ⟨g, hg⟩ := LocalPairs.SylowPointwise.isInner_of_fixes_sylow
    Realization.normalizer_surjective S a (fun x hx => ha ⟨x, hx⟩)
  exact ⟨g, hg.symm⟩

end Held
