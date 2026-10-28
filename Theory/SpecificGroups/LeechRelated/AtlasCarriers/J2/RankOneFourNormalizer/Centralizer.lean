module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RankOneFourNormalizer.Checks

/-!
# The centralizer of the fixed Hall–Janko radical is a two-group

Positive-word induction on the shared normalizer candidate lifts the eighteen
checked quotient representatives. Commutation with the six radical generators
excludes every coset outside the radical. Thus its centralizer embeds in the
already certified group of order 64.

This is the inner-group part of NormalizerAction/PointwiseFixer.lean, adapted
here so that no full-automorphism realization is needed. The original file
and all ATLAS data are preserved. Original proof code: repository Apache 2.0.
Source: GLS3 Table 5.3g; Aschbacher–Smith 15.3.43, printed p.1140.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.RankOneFourNormalizer
open Theory.GroupTheory Subgroup ExceptionalParabolics GeneratorPair Seed PairNormalizer
open PairNormalizer.RadicalData PairNormalizer.CandidateQuotient
open GeneratorPair.SecondOrbitCertificate

private def representative (i : Fin 18) : Carrier := evalWord normalizerGenerator (repWord i)

private theorem generator_inclusion (i : Fin 3) :
    inclusion (normalizerGenerator i) =
      ![SylowData.tTable, QuotientData.oddTable 0, QuotientData.oddTable 1] i := by
  fin_cases i
  · exact (sGenerator_inclusion 3).trans (by decide +kernel)
  · exact oddGenerator_inclusion 0
  · exact oddGenerator_inclusion 1

private theorem representative_inclusion (i : Fin 18) : inclusion (representative i) = repTable i := by
  have hw (w : List (Fin 3)) : inclusion (evalWord normalizerGenerator w) =
      evalWord ![SylowData.tTable, QuotientData.oddTable 0, QuotientData.oddTable 1] w := by
    induction w with
    | nil => exact map_one inclusion
    | cons j w ih => rw [evalWord, map_mul, generator_inclusion, ih, evalWord]
  exact hw (repWord i)

private theorem representative_mul (i j : Fin 18) :
    representative i * representative j =
      qElement (radicalFactor i j) * representative (mulIndex i j) := by
  apply inclusion_injective
  rw [map_mul, map_mul, representative_inclusion, representative_inclusion,
    representative_inclusion, qElement_inclusion]
  exact repTable_mul i j

/-- Positive-word induction lifts the eighteen checked quotient representatives. -/
private theorem normalizer_coverage {x : Carrier} (hx : x ∈ p₂) :
    ∃ q ∈ q₂, ∃ i : Fin 18, q * representative i = x := by
  rw [full_normalizer_eq_candidate] at hx
  have he : candidate = closure ((q₂ : Set Carrier) ∪ Set.range normalizerGenerator) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq]
    rfl
  rw [he] at hx
  change x ∈ (Subgroup.closure _).toSubmonoid at hx
  rw [closure_toSubmonoid_of_finite] at hx
  induction hx using Submonoid.closure_induction_left with
  | one => exact ⟨1, q₂.one_mem, 0, one_mul 1⟩
  | mul_left g hg y _ ih =>
    obtain ⟨q, hq, i, rfl⟩ := ih
    rcases hg with hg | ⟨j, rfl⟩
    · exact ⟨g * q, q₂.mul_mem hg hq, i, mul_assoc _ _ _⟩
    · let k : Fin 18 := ![9, 3, 1] j
      have hk : representative k = normalizerGenerator j := by
        fin_cases j <;> simp [k, representative, repWord]
      have hconj : normalizerGenerator j * q * (normalizerGenerator j)⁻¹ ∈ q₂ :=
        (mem_normalizer_iff.mp (normalizerGenerator_mem_p₂ j) q).mp hq
      refine ⟨(normalizerGenerator j * q * (normalizerGenerator j)⁻¹) *
        qElement (radicalFactor k i), q₂.mul_mem hconj (qElement_mem _), mulIndex k i, ?_⟩
      rw [mul_assoc, ← representative_mul, hk]
      group

theorem centralizer_le_q₂ : centralizer (q₂ : Set Carrier) ≤ q₂ := by
  intro x hx
  have hn : x ∈ p₂ := centralizer_le_normalizer _ hx
  obtain ⟨q, hq, j, hj⟩ := normalizer_coverage hn
  obtain ⟨i, hi⟩ := exists_qElement hq
  have ht : inclusion x = qTable i * repTable j := by
    rw [← hj, ← hi, map_mul, qElement_inclusion, representative_inclusion]
  have hj0 := Checks.centralizer_check i j (by
    intro k
    have hc := mem_centralizer_iff.mp hx (q₂Generator k) (subset_closure ⟨k, rfl⟩)
    have he := congrArg inclusion hc.symm
    rw [map_mul, map_mul, ht, q₂Generator_inclusion] at he
    exact ⟨congrArg (fun p : Equiv.Perm (Fin 100) => p 0) he,
      congrArg (fun p : Equiv.Perm (Fin 100) => p 1) he⟩)
  subst j
  simpa [representative, repWord] using hj ▸ hq

theorem centralizer_isPGroup : IsPGroup 2 (centralizer (q₂ : Set Carrier)) :=
  q₂_isPGroup.of_injective (Subgroup.inclusion centralizer_le_q₂)
    (Subgroup.inclusion_injective centralizer_le_q₂)

end Sporadic.LeechRelated.J2.RankOneFourNormalizer
