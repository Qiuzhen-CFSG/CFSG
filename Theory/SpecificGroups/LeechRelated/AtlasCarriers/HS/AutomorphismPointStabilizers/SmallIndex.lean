module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.CarrierComparison
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.DoubleCosets
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Elementary
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.Generation
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.PrimeOvergroups
public import Mathlib.GroupTheory.Index

/-!
# The small-index calculation for the HS point stabilizer

This module assembles the finite-certificate route to divisibility by eleven
for maximal proper subgroups of index at most 100. The auxiliary stabilizer
has a specified cyclic subgroup P of order eleven and a subgroup N normalizing
P. Covering by N-double cosets, generation by pairs of conjugates of P, and a
large index for the exceptional overgroup imply the result by the coset-action
argument in `PrimeOvergroups`.

The final theorem supplies all these certificates and transfers the result
through the permutation-preserving equivalence between the auxiliary group
and the actual point stabilizer. It has no additional model hypotheses and
provides exactly the premise of `HS.pointStabilizer_map_of_smallMaximalIndex`.
The latter consumer is deliberately not imported, avoiding a dependency cycle.

Source context: GLS3 Table 5.3m, printed p.274, and Aschbacher–Smith printed
pp.33 and 510. All subgroups and indices below are inside the point stabilizer
or its explicitly compared auxiliary group. Neither automorphism coverage nor
an identification with a Mathieu carrier is assumed.
-/

public section
namespace Sporadic.LeechRelated.HS.SmallIndex
open Subgroup

/-- The finite coverage and recovery certificates suffice in the auxiliary group. -/
theorem properIndex_dvd_of_certificate
    (hNL : normalizerCandidate ≤ exceptionalSubgroup)
    (hlarge : 100 < exceptionalSubgroup.index)
    (hcover : ∀ g : CertifiedStabilizer, ∃ i a b,
      a ∈ normalizerCandidate ∧ b ∈ normalizerCandidate ∧ g = a * representative i * b)
    (hrecover : ∀ i, representative i ∈ exceptionalSubgroup ∨
      primeSubgroup ⊔ primeSubgroup.map
        (MulAut.conj (representative i)).toMonoidHom = ⊤)
    (K : Subgroup CertifiedStabilizer) (hK : K ≠ ⊤) (hi : K.index ≤ 100) :
    11 ∣ K.index := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hgen := pairGeneration_of_normalizing_doubleCosets
    primeSubgroup normalizerCandidate exceptionalSubgroup normalizerCandidate_le_normalizer
    hNL representative hcover (by simpa only [MulEquiv.toMonoidHom_eq_coe] using hrecover)
  exact dvd_index_of_large_overgroup primeSubgroup exceptionalSubgroup
    primeSubgroup_isPGroup hlarge (le_of_pairGeneration _ _ hgen) K hK hi

/-- An actual carrier comparison transfers the finite certificate calculation to HS. -/
theorem pointStabilizer_smallMaximalIndex_of_certificate
    (e : pointStabilizer ≃* CertifiedStabilizer)
    (hNL : normalizerCandidate ≤ exceptionalSubgroup)
    (hlarge : 100 < exceptionalSubgroup.index)
    (hcover : ∀ g : CertifiedStabilizer, ∃ i a b,
      a ∈ normalizerCandidate ∧ b ∈ normalizerCandidate ∧ g = a * representative i * b)
    (hrecover : ∀ i, representative i ∈ exceptionalSubgroup ∨
      primeSubgroup ⊔ primeSubgroup.map
        (MulAut.conj (representative i)).toMonoidHom = ⊤) :
    ∀ K : Subgroup pointStabilizer, IsCoatom K → K.index ≤ 100 → 11 ∣ K.index := by
  intro K hK hi
  have hproper : K.map (e : pointStabilizer →* CertifiedStabilizer) ≠ ⊤ := by
    intro ht
    apply hK.ne_top
    apply map_injective (f := (e : pointStabilizer →* CertifiedStabilizer)) e.injective
    rw [ht, map_top_of_surjective _ e.surjective]
  have hsmall : (K.map (e : pointStabilizer →* CertifiedStabilizer)).index ≤ 100 := by
    simpa only [index_map_equiv] using hi
  have h := properIndex_dvd_of_certificate hNL hlarge hcover hrecover _ hproper hsmall
  simpa only [index_map_equiv] using h

/-- Every maximal proper subgroup of the actual HS point stabilizer with index
at most 100 has index divisible by eleven. All indices are inside the stabilizer. -/
theorem pointStabilizer_smallMaximalIndex :
    ∀ K : Subgroup pointStabilizer, IsCoatom K → K.index ≤ 100 → 11 ∣ K.index :=
  pointStabilizer_smallMaximalIndex_of_certificate pointStabilizerEquivCertified
    normalizerCandidate_le_exceptionalSubgroup exceptionalSubgroup_index_gt
    normalizerCandidate_doubleCosetCover representative_mem_or_pair_eq_top

end Sporadic.LeechRelated.HS.SmallIndex
