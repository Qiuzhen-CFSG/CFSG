module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Reduction
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups

/-!
# Held Sylows and the full permutation normalizer

The certified representative calculations give centers of order two and
self-normalizing Sylow two-subgroups in the literal ATLAS Held carrier. The
full-normalizer centralizer certificate also controls the centers of Sylow
two-subgroups in the full permutation normalizer. The orbit calculation
excludes proper 3′-overgroups of a Held Sylow.

Using the actual inclusion of Held, the transfer reductions construct a
Sylow of the full normalizer as the normalizer of an embedded Held Sylow,
with exactly the original Sylow as inverse image. They also establish
self-normalization and the normalized 3′-subgroup assertion in the full
normalizer. The sole premise is that its quotient by the relatively normal
Held copy has order at most two; simplicity, perfectness and abstract
automorphism realization are not needed.

`sylow_geometry` assembles all four assertions for the local-pair consumer.
Transport to abstract automorphisms and discharge of the quotient bound
belong to that consumer.

Source: GLS3 Table 5.3p and the Held-case applications in Aschbacher–Smith,
printed pp.725, 748 and 1163–1164.
-/

public section

namespace Held.LocalPairs.SylowGeometry
open Subgroup

/-- The center of every Sylow two-subgroup of the literal Held carrier has order two. -/
theorem inner_center_card (S : Sylow 2 He) : Nat.card (center S) = 2 :=
  Calculations.inner_center_card S

/-- The center of every Sylow two-subgroup of the full permutation normalizer
has order two, under the bound on the actual normalizer quotient. -/
theorem normalizer_center_card
    (hbound : Nat.card PermutationNormalizerQuotient ≤ 2)
    (T : Sylow 2 PermutationNormalizer) : Nat.card (center T) = 2 :=
  Calculations.normalizer_center_card hbound T

/-- Sylow two-subgroups are self-normalizing in the full permutation normalizer. -/
theorem normalizer_self_normalizing
    (hbound : Nat.card PermutationNormalizerQuotient ≤ 2)
    (T : Sylow 2 PermutationNormalizer) :
    normalizer (T : Set PermutationNormalizer) = (T : Subgroup PermutationNormalizer) :=
  self_normalizing_of_inner_self_normalizing hbound Calculations.inner_self_normalizing T

/-- The full normalizer of an embedded Held Sylow is Sylow in the permutation
normalizer, and its inverse image in Held is precisely the original Sylow. -/
theorem exists_normalizer_sylow
    (hbound : Nat.card PermutationNormalizerQuotient ≤ 2)
    (S : Sylow 2 He) :
    ∃ T : Sylow 2 PermutationNormalizer,
      (T : Subgroup PermutationNormalizer) =
        normalizer (S.map innerEmbedding : Set PermutationNormalizer) ∧
      T.comap innerEmbedding = (S : Subgroup He) :=
  exists_normalizer_sylow_of_self_normalizing hbound S (Calculations.inner_self_normalizing S)

/-- The complete conditional Held Sylow package: both center orders, full
Sylow self-normalization, the normalized 3′-subgroup assertion, and the exact
normalizer construction with its inverse image under the literal inclusion. -/
theorem sylow_geometry (hbound : Nat.card PermutationNormalizerQuotient ≤ 2) :
    (∀ S : Sylow 2 He, Nat.card (center S) = 2) ∧
    (∀ T : Sylow 2 PermutationNormalizer,
      Nat.card (center T) = 2 ∧
      normalizer (T : Set PermutationNormalizer) = (T : Subgroup PermutationNormalizer)) ∧
    (∀ (T : Sylow 2 PermutationNormalizer) (U : Subgroup PermutationNormalizer),
      (T : Subgroup PermutationNormalizer) ≤ normalizer (U : Set PermutationNormalizer) →
      ¬ 3 ∣ Nat.card U → IsPGroup 2 U) ∧
    (∀ S : Sylow 2 He, ∃ T : Sylow 2 PermutationNormalizer,
      (T : Subgroup PermutationNormalizer) =
        normalizer (S.map innerEmbedding : Set PermutationNormalizer) ∧
      T.comap innerEmbedding = (S : Subgroup He)) :=
  ⟨inner_center_card,
    fun T => ⟨normalizer_center_card hbound T, normalizer_self_normalizing hbound T⟩,
    normalized_three_prime_isPGroup hbound, exists_normalizer_sylow hbound⟩

end Held.LocalPairs.SylowGeometry
