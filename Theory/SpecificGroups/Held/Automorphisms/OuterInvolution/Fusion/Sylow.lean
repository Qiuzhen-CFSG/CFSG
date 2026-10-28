module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Fusion.Normalizer
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Fusion.Words
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.WordCoverage

/-!
# Exhaustion of the outer coset in a full-normalizer Sylow subgroup

The full normalizer of the embedded, self-normalizing Held Sylow is Sylow
in the full permutation normalizer. Its intersection with Held is exactly
that original subgroup. Any outer element in it therefore represents the
other coset, which is exhausted by the already checked 1024 binary words.
The normalization of the particular outer word is a separate finite check.
Source: GLS3 Table 5.3p; the fixed ATLAS HeG1-p2058B0 carrier.
-/

@[expose] public section
namespace Held.OuterInvolution.Fusion
open Subgroup LocalPairs LocalPairs.SylowGeometry
open TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration

def fullSylow : Subgroup PermutationNormalizer :=
  normalizer (Calculations.representative.map innerEmbedding : Set PermutationNormalizer)

theorem outer_not_mem_inner : outer ∉ innerSubgroup := by
  intro h
  have hm := (inferInstance : innerSubgroup.Normal).conj_mem outer h (innerEmbedding shift)⁻¹
  apply representative_not_mem_inner
  simpa only [outer, MulAut.conj_apply, inv_inv, mul_assoc, inv_mul_cancel_left,
    inv_mul_cancel, mul_one] using hm

theorem exists_fullSylow : ∃ P : Sylow 2 PermutationNormalizer,
    (P : Subgroup PermutationNormalizer) = fullSylow := by
  obtain ⟨S, hS⟩ := Calculations.exists_representative_sylow
    Calculations.representative_isPGroup Calculations.InnerNormalizer.normalizer_eq
  obtain ⟨P, hP, _⟩ := exists_normalizer_sylow_of_self_normalizing
    normalizerQuotient_card_le_two S (Calculations.inner_self_normalizing S)
  exact ⟨P, by simpa only [hS, fullSylow] using hP⟩

theorem fullSylow_comap : fullSylow.comap innerEmbedding = Calculations.representative := by
  rw [fullSylow, normalizer_comap_inner, Calculations.InnerNormalizer.normalizer_eq]

theorem fullSylow_oddWord_coverage (ht : outer ∈ fullSylow)
    (n : PermutationNormalizer) (hn : n ∈ fullSylow) (hout : n ∉ innerSubgroup) :
    ∃ i : Fin 1024, oddWord i = n := by
  obtain ⟨g, hg⟩ := exists_inner_mul outer n outer_not_mem_inner hout
  have hgS : g ∈ Calculations.representative := by
    rw [← fullSylow_comap]
    change innerEmbedding g ∈ fullSylow
    have hm := fullSylow.mul_mem hn (fullSylow.inv_mem ht)
    rwa [← hg, mul_inv_cancel_right] at hm
  obtain ⟨i, hi⟩ := normalForm_surjective ⟨g, hgS⟩
  refine ⟨i, ?_⟩
  rw [oddWord, hi]
  exact hg
end Held.OuterInvolution.Fusion
