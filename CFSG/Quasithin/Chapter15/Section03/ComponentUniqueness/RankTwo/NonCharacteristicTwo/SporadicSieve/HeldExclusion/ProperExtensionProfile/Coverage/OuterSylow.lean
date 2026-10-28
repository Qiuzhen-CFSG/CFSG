module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.Representatives
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Reduction
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.WordCoverage
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors

/-!
# A Sylow marking in the full automorphism group of Held

The existing 1024-word cover bounds the order of a certified inner Sylow.
The literal pure even candidate has order 1024, so a Sylow containing it
must equal it. Its self-normalization in Held lets the full permutation
normalizer construction lift it to a Sylow of that normalizer. Surjective
realization then carries this Sylow onto the full automorphism stabilizer.

Only realization and the independent bound on the full normalizer quotient
are assumed. No order formula for Held, maximal-local catalogue, enumeration
of elementary subgroups, or proper-extension coverage is used.
Source: Aschbacher--Smith 15.3.41--42, printed p.1138; GLS3 Table 5.3p;
the existing literal Held Sylow and candidate-order certificates.
-/

public section
open Subgroup Held Held.LocalPairs Held.LocalPairs.PairCoverage.LocalActions
open Held.LocalPairs.SylowGeometry.Calculations
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.CoverageData

/-- The literal even subgroup is Sylow, using the existing inner word-cover bound. -/
theorem pureTwo_sylow : ∃ S : Sylow 2 He, (S : Subgroup He) = pureTwo := by
  have hp : IsPGroup 2 (candidateTwo false 0) :=
    IsPGroup.of_card (n := 10) (Exhaustion.candidateFactorOrders false 0).1
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  obtain ⟨P, hP⟩ := exists_representative_sylow representative_isPGroup
    InnerNormalizer.normalizer_eq
  have hc : Nat.card T ≤ 1024 := by
    calc
      Nat.card T = Nat.card P := Nat.card_congr (T.equiv P).toEquiv
      _ = Nat.card representative := by rw [hP]
      _ ≤ 1024 := by
        simpa using Nat.card_le_card_of_surjective _
          Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.normalForm_surjective
  exact ⟨T, (eq_of_le_of_card_ge hT (by rw [(Exhaustion.candidateFactorOrders false 0).1]; exact hc)).symm⟩

private theorem map_normalizer (hreal : Function.Surjective permutationGroup.normalizerMonoidHom)
    (S : Subgroup He) :
    (normalizer (S.map innerEmbedding : Set PermutationNormalizer)).map
      permutationGroup.normalizerMonoidHom = automorphismNormalizer S := by
  have hc : (automorphismNormalizer S).comap permutationGroup.normalizerMonoidHom =
      normalizer (S.map innerEmbedding : Set PermutationNormalizer) := by
    have he : ((normalizer (S.map representation : Set (Equiv.Perm (Fin 2058)))).comap
        (normalizer (permutationGroup : Set (Equiv.Perm (Fin 2058)))).subtype) =
        normalizer (S.map innerEmbedding : Set PermutationNormalizer) := by
      rw [comap_normalizer_eq_of_le_range]
      · congr 1
        have hf : (normalizer (permutationGroup : Set (Equiv.Perm (Fin 2058)))).subtype.comp
            innerEmbedding = representation := rfl
        rw [← hf, ← map_map, comap_map_eq_self_of_injective Subtype.val_injective]
      · rintro _ ⟨s, hs, rfl⟩
        exact ⟨innerEmbedding s, rfl⟩
    rw [← he]
    ext a
    exact normalizerAction_mem_stabilizer_iff permutationGroup S a
  rw [← hc, map_comap_eq, MonoidHom.range_eq_top.mpr hreal, top_inf_eq]

/-- The full automorphism stabilizer is Sylow under the independent realization and quotient bound. -/
theorem outerRepresentative_sylow
    (hreal : Function.Surjective permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card PermutationNormalizerQuotient ≤ 2) :
    ∃ T : Sylow 2 (MulAut He), (T : Subgroup (MulAut He)) =
      outerRepresentative := by
  obtain ⟨S, hS⟩ := pureTwo_sylow
  obtain ⟨P, hP, _⟩ := SylowGeometry.exists_normalizer_sylow_of_self_normalizing
    hbound S (inner_self_normalizing S)
  refine ⟨P.mapSurjective hreal, ?_⟩
  change (P : Subgroup PermutationNormalizer).map permutationGroup.normalizerMonoidHom = _
  rw [hP, hS, map_normalizer hreal]
  rfl

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.CoverageData
