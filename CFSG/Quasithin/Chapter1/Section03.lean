module

public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.PGroupCore

/-!
# Solvable uniqueness subgroups: the maximality argument

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §1.3, especially Theorem 1.3.7, printed p. 512.

This module currently proves the maximality step with its explicit mathematical
inputs. Nontriviality of the two-core gives a two-local overgroup of the
normalizer. Normality in every maximal two-local overgroup then identifies the
normalizer with the unique such overgroup. The source application will discharge
normality using Proposition 1.3.5 and nontriviality using membership in `He`.
The embedding analysis of Proposition 1.3.4 and the results 1.3.8--1.3.9 remain
separate prerequisites; this intermediate result does not assert them.
-/

namespace CFSG.Quasithin.Chapter1.Section03

/-- The maximality step of 1.3.7, with explicit two-core and normality hypotheses. -/
public theorem normalizer_unique_of_normal_in_maximalTwoLocals
    {G : Type*} [Group G] [Finite G] (X T : Subgroup G)
    (hT : T ≤ Subgroup.normalizer (X : Set G))
    (hcore : pCore 2 X ≠ ⊥)
    (hnormal : ∀ M : Subgroup G, IsMaximalTwoLocal M → X ⊔ T ≤ M →
      (X.subgroupOf M).Normal) :
    IsMaximalTwoLocal (Subgroup.normalizer (X : Set G)) ∧
      {M : Subgroup G | IsMaximalTwoLocal M ∧ X ⊔ T ≤ M} =
        {Subgroup.normalizer (X : Set G)} := by
  exact Subgroup.unique_maximalTwoLocal_overgroup_of_normal X T hT
    (Subgroup.exists_twoLocal_overgroup_normalizer X (pCore 2 X) hcore pCore_isPGroup)
    hnormal

end CFSG.Quasithin.Chapter1.Section03
