module

public import Theory.Representation.BinaryQuarticMathieu.RankRecognition.Data

/-!
# Assembly from representative histograms and quartic-preserving transports

Invariance of the genuine contraction statistic propagates the four
representative calculations along preserving linear equivalences. The checked
word enumeration then gives exhaustive histograms, their multiplicities, and
recognition of the marked points.

The inputs corresponding to `../source/orbit-witnesses.json` remain explicit:
actual quartic-preserving transports, and actual representative histograms.
This module proves conditional assembly only. Its consumer must construct both
inputs before asserting unconditional recognition or rank classification.
-/

public section

namespace BinaryQuarticMathieu.RankRecognition

/-- Transport representative histograms along actual quartic preservers. -/
theorem word_distributions_of_transports
    (hrep : ∀ c : Fin 4,
      rankDistribution quartic (decode (representative c)) = profile c)
    (htransport : ∀ n : Word, ∃ g : U ≃ₗ[F] U,
      Preserves quartic g ∧ g (decode (representative (wordClass n))) = decode n)
    (n : Word) : rankDistribution quartic (decode n) = profile (wordClass n) := by
  obtain ⟨g, hg, hn⟩ := htransport n
  rw [← hn, rankDistribution_invariant hg, hrep]

/-- Exhaustiveness follows from the checked enumeration of the actual space. -/
theorem distributions_exhaustive_of_words
    (h : ∀ n : Word, rankDistribution quartic (decode n) = profile (wordClass n))
    (v : U) : ∃ c : Fin 4, rankDistribution quartic v = profile c := by
  obtain ⟨n, rfl⟩ := decode_bijective.surjective v
  exact ⟨wordClass n, h n⟩

/-- Once representative calculations and transports are discharged, the label
counts become counts of the intrinsic contraction histograms. -/
theorem distribution_card_of_words
    (h : ∀ n : Word, rankDistribution quartic (decode n) = profile (wordClass n))
    (c : Fin 4) : Nat.card {v : U // rankDistribution quartic v = profile c} =
      classSize c := by
  have e : {n : Word // wordClass n = c} ≃
      {v : U // rankDistribution quartic v = profile c} :=
    decodeEquiv.subtypeEquiv (fun n => by
      change wordClass n = c ↔ rankDistribution quartic (decode n) = profile c
      rw [h n, profile_injective.eq_iff])
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact wordClass_counts c

/-- The checked point marking identifies precisely the class with the
point histogram, conditional on the still separate histogram certificates. -/
theorem recognition_of_words
    (h : ∀ n : Word, rankDistribution quartic (decode n) = profile (wordClass n))
    (v : U) : rankDistribution quartic v = pointDistribution ↔ v ∈ Set.range point := by
  obtain ⟨n, rfl⟩ := decode_bijective.surjective v
  change rankDistribution quartic (decode n) = profile 3 ↔ _
  rw [h n, profile_injective.eq_iff, wordClass_point_iff]

/-- The zero histogram occurs only at zero, once the nonzero histograms have
been computed and propagated. -/
theorem zero_distribution_iff_of_words
    (h : ∀ n : Word, rankDistribution quartic (decode n) = profile (wordClass n))
    (v : U) : rankDistribution quartic v = zeroDistribution ↔ v = 0 := by
  obtain ⟨n, rfl⟩ := decode_bijective.surjective v
  change rankDistribution quartic (decode n) = profile 0 ↔ _
  rw [h n, profile_injective.eq_iff, wordClass_zero_iff]
  have hz : decode 0 = 0 := by decide +kernel
  rw [← hz, decode_injective.eq_iff]

end BinaryQuarticMathieu.RankRecognition
