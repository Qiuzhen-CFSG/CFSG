module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.QuotientSeed
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.NormalizerCoverage.Words

/-!
# Full coverage of the fixed Hall--Janko radical normalizer

The shared candidate is exactly the full normalizer of the unchanged `Seed.q₂`
in the degree-100 ATLAS carrier. A certified right-coset cover of the whole
carrier has 525 representatives. For every nonidentity representative, the
conjugate of a specified radical generator lies outside all 64 radical words;
three permutation coordinates certify this. Hence a normalizing element can
only lie in the identity coset of the candidate.

This proves coverage independently of quotient recognition, group order, and
the intrinsic calculations for `l₂`. Source: GLS3 Table 5.3g and
Aschbacher--Smith, printed p.511 (PDF p.528). The ATLAS J2G1-p100B0 words and
reproducible certificate generator are retained in `NormalizerCoverage/source/`.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer
open GeneratorPair Seed NormalizerCoverage NormalizerCoverage.Data

private theorem repr_index_zero_of_normalizes (i : Fin 525)
    (hi : NormalizerCoverage.repr i ∈ p₂) : i = 0 := by
  by_contra hn
  have hg : q₂Generator (badGenerator i) ∈ q₂ := Subgroup.subset_closure ⟨_, rfl⟩
  have hc : NormalizerCoverage.repr i * q₂Generator (badGenerator i) *
      (NormalizerCoverage.repr i)⁻¹ ∈ q₂ :=
    ((Subgroup.mem_normalizer_iff.mp hi) _).mp hg
  obtain ⟨k, hk⟩ := exists_qElement hc
  have he : NormalizerCoverage.repr i * q₂Generator (badGenerator i) =
      qElement k * NormalizerCoverage.repr i := by
    rw [hk]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  have hp : fingerprint (fun p => Data.reprMap i (RadicalData.qGenTable (badGenerator i) p)) =
      fingerprint (fun p => RadicalData.qTable k (Data.reprMap i p)) := by
    apply congrArg fingerprint
    funext p
    have h := congrArg (fun x : Carrier => inclusion x p) he
    simpa only [map_mul, Equiv.Perm.mul_apply, q₂Generator_inclusion,
      qElement_inclusion, repr_spec] using h
  exact separation_check i hn k hp

/-- Every element of the full normalizer of the fixed radical lies in the shared candidate. -/
theorem full_normalizer_le_candidate : Seed.p₂ ≤ candidate := by
  intro x hx
  obtain ⟨h, i, he⟩ := NormalizerCoverage.covers x
  have hr : NormalizerCoverage.repr i ∈ p₂ := by
    have hm := p₂.mul_mem (p₂.inv_mem (candidate_le_p₂ h.property)) hx
    simpa only [he, inv_mul_cancel_left] using hm
  have hi := repr_index_zero_of_normalizes i hr
  simpa only [he, hi, repr_zero, mul_one] using h.property

/-- The concrete generated subgroup is the actual full radical normalizer. -/
theorem full_normalizer_eq_candidate : Seed.p₂ = candidate :=
  le_antisymm full_normalizer_le_candidate candidate_le_p₂

end Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer
