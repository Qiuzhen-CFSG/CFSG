module

public import Theory.SpecificGroups.Held.LocalPairs.Transport
public import Theory.SpecificGroups.Held.LocalPairs.Faithfulness
public import Theory.SpecificGroups.Held.Automorphisms.Reduction
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Sylow transfer to the full Held permutation normalizer

The embedded Held group is normal in its full permutation normalizer. If
that quotient has order at most two, a subgroup of the normalizer is a
two-group as soon as its inverse image in Held is a two-group. We prove this
by lifting powers through the quotient, using the actual inner embedding.

Normality identifies the intersection of an ambient Sylow with Held as an
inner Sylow. Consequently, a self-normalizing Sylow of Held has a full
normalizer which is Sylow in the permutation normalizer, with exactly the
original Sylow as inverse image. Intersecting with the normal Held subgroup
also proves self-normalization of the ambient Sylow. No realization of
abstract automorphisms is needed.

The same transfer reduces normalized 3′-subgroups to Held. A product-order
argument identifies the remaining inner assertion with the absence of
proper 3′-overgroups of a Held Sylow. These are conditional transfers;
concrete Sylow centers and the inner normalizer and overgroup calculations
remain separate mathematical inputs.

Sources: the actual ATLAS HeG1-p2058B0 carrier; GLS3 Table 5.3p,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`; the Held-case local obligations in
Aschbacher–Smith, printed pp.725, 748 and 1163–1164.
-/

public section

namespace Held.LocalPairs.SylowGeometry
open Subgroup

/-- The relatively normal copy of Held used in the full normalizer quotient. -/
abbrev innerSubgroup : Subgroup PermutationNormalizer :=
  permutationGroup.subgroupOf (normalizer (permutationGroup : Set (Equiv.Perm (Fin 2058))))

/-- The actual inclusion of Held into its permutation normalizer is injective. -/
theorem innerEmbedding_injective : Function.Injective innerEmbedding :=
  inclusion_injective _

/-- The image is exactly the denominator of `PermutationNormalizerQuotient`. -/
theorem innerEmbedding_range : innerEmbedding.range = innerSubgroup := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact g.property
  · intro hx
    exact ⟨⟨x.val, hx⟩, rfl⟩

private instance innerRange_normal : innerEmbedding.range.Normal := by
  rw [innerEmbedding_range]
  infer_instance

/-- A full normalizer quotient of order at most two is a two-group. -/
theorem quotient_isPGroup (hbound : Nat.card PermutationNormalizerQuotient ≤ 2) :
    IsPGroup 2 PermutationNormalizerQuotient := by
  have hpos : 0 < Nat.card PermutationNormalizerQuotient := Nat.card_pos
  have h : Nat.card PermutationNormalizerQuotient = 1 ∨
      Nat.card PermutationNormalizerQuotient = 2 := by omega
  rcases h with h | h
  · exact IsPGroup.of_card (n := 0) h
  · exact IsPGroup.of_card (n := 1) h

/-- Lift powers through the full normalizer quotient to test two-subgroups inside Held. -/
theorem isPGroup_of_comap_inner
    (hbound : Nat.card PermutationNormalizerQuotient ≤ 2)
    (U : Subgroup PermutationNormalizer) (hU : IsPGroup 2 (U.comap innerEmbedding)) :
    IsPGroup 2 U := by
  intro u
  let q : PermutationNormalizer →* PermutationNormalizerQuotient :=
    QuotientGroup.mk' innerSubgroup
  obtain ⟨n, hn⟩ := quotient_isPGroup hbound (q u)
  have hmem : (u : PermutationNormalizer) ^ 2 ^ n ∈ innerSubgroup := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q ((u : PermutationNormalizer) ^ 2 ^ n) = 1
    rwa [map_pow]
  rw [← innerEmbedding_range] at hmem
  obtain ⟨g, hg⟩ := hmem
  have hgU : g ∈ U.comap innerEmbedding := by
    change innerEmbedding g ∈ U
    rw [hg]
    exact U.pow_mem u.property _
  obtain ⟨m, hm⟩ := hU ⟨g, hgU⟩
  refine ⟨n + m, Subtype.ext ?_⟩
  change (u : PermutationNormalizer) ^ 2 ^ (n + m) = 1
  rw [pow_add, pow_mul, ← hg]
  have hmg : g ^ 2 ^ m = 1 := congrArg Subtype.val hm
  rw [← map_pow, hmg, map_one]

/-- The inverse image of the full normalizer of an embedded subgroup is its Held normalizer. -/
theorem normalizer_comap_inner (S : Subgroup He) :
    (normalizer (S.map innerEmbedding : Set PermutationNormalizer)).comap innerEmbedding =
      normalizer (S : Set He) := by
  rw [comap_normalizer_eq_of_le_range (map_le_range _ _),
    comap_map_eq_self_of_injective innerEmbedding_injective]

/-- Every subgroup normalizes its intersection with the relatively normal Held copy. -/
theorem normalizes_inner_intersection (T : Subgroup PermutationNormalizer) :
    T ≤ normalizer ((T.comap innerEmbedding).map innerEmbedding : Set PermutationNormalizer) := by
  rw [map_comap_eq]
  exact (le_inf le_normalizer_of_normal le_normalizer).trans
    inf_normalizer_le_normalizer_inf

/-- An ambient Sylow intersects the Held copy in an actual Sylow of Held. -/
theorem exists_inner_sylow (T : Sylow 2 PermutationNormalizer) :
    ∃ S : Sylow 2 He, (S : Subgroup He) = T.comap innerEmbedding := by
  obtain ⟨Q, hQ⟩ := T.exists_subgroupOf_eq_of_normal innerEmbedding.range
  let e := MonoidHom.ofInjective innerEmbedding_injective
  refine ⟨Q.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective, ?_⟩
  change (Q : Subgroup innerEmbedding.range).map e.symm.toMonoidHom = _
  rw [hQ]
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    change innerEmbedding (e.symm x) ∈ T
    rw [MonoidHom.apply_ofInjective_symm]
    exact hx
  · intro hg
    refine ⟨e g, ?_, e.symm_apply_apply g⟩
    exact hg

/-- Construct the larger Sylow as the full normalizer of the embedded inner Sylow.
Its inverse image is the original Sylow; no equality of these two ambient subgroups is asserted. -/
theorem exists_normalizer_sylow_of_self_normalizing
    (hbound : Nat.card PermutationNormalizerQuotient ≤ 2)
    (S : Sylow 2 He) (hS : normalizer (S : Set He) = (S : Subgroup He)) :
    ∃ T : Sylow 2 PermutationNormalizer,
      (T : Subgroup PermutationNormalizer) =
        normalizer (S.map innerEmbedding : Set PermutationNormalizer) ∧
      T.comap innerEmbedding = (S : Subgroup He) := by
  obtain ⟨T, hT⟩ := S.exists_comap_eq_of_injective innerEmbedding_injective
  have hTN : (T : Subgroup PermutationNormalizer) ≤
      normalizer (S.map innerEmbedding : Set PermutationNormalizer) := by
    rw [← hT]
    exact normalizes_inner_intersection T
  have hNp : IsPGroup 2
      (normalizer (S.map innerEmbedding : Set PermutationNormalizer)) := by
    apply isPGroup_of_comap_inner hbound
    rw [normalizer_comap_inner]
    change IsPGroup 2 (normalizer (S : Set He))
    rw [hS]
    exact S.isPGroup'
  exact ⟨T, (T.3 hNp hTN).symm, hT⟩

/-- Self-normalization of inner Sylows forces self-normalization of all full-normalizer Sylows. -/
theorem self_normalizing_of_inner_self_normalizing
    (hbound : Nat.card PermutationNormalizerQuotient ≤ 2)
    (hinner : ∀ S : Sylow 2 He, normalizer (S : Set He) = (S : Subgroup He))
    (T : Sylow 2 PermutationNormalizer) :
    normalizer (T : Set PermutationNormalizer) = (T : Subgroup PermutationNormalizer) := by
  obtain ⟨S, hS⟩ := exists_inner_sylow T
  have hTN : (T : Subgroup PermutationNormalizer) ≤
      normalizer (S.map innerEmbedding : Set PermutationNormalizer) := by
    rw [hS]
    exact normalizes_inner_intersection T
  have hNp : IsPGroup 2
      (normalizer (S.map innerEmbedding : Set PermutationNormalizer)) := by
    apply isPGroup_of_comap_inner hbound
    rw [normalizer_comap_inner]
    change IsPGroup 2 (normalizer (S : Set He))
    rw [hinner]
    exact S.isPGroup'
  have hN := T.3 hNp hTN
  apply le_antisymm _ le_normalizer
  calc
    normalizer (T : Set PermutationNormalizer) ≤
        normalizer ((T.comap innerEmbedding).map innerEmbedding : Set PermutationNormalizer) := by
      rw [map_comap_eq]
      exact (le_inf le_normalizer_of_normal le_rfl).trans
        inf_normalizer_le_normalizer_inf
    _ = normalizer (S.map innerEmbedding : Set PermutationNormalizer) := by rw [← hS]
    _ = (T : Subgroup PermutationNormalizer) := hN

/-- Transfer the normalized 3′-subgroup assertion from Held to its full permutation normalizer. -/
theorem normalized_three_prime_isPGroup_of_inner
    (hbound : Nat.card PermutationNormalizerQuotient ≤ 2)
    (hinner : ∀ (S : Sylow 2 He) (V : Subgroup He),
      (S : Subgroup He) ≤ normalizer (V : Set He) → ¬ 3 ∣ Nat.card V → IsPGroup 2 V)
    (T : Sylow 2 PermutationNormalizer) (U : Subgroup PermutationNormalizer)
    (hnorm : (T : Subgroup PermutationNormalizer) ≤ normalizer (U : Set PermutationNormalizer))
    (hthree : ¬ 3 ∣ Nat.card U) : IsPGroup 2 U := by
  obtain ⟨S, hS⟩ := exists_inner_sylow T
  apply isPGroup_of_comap_inner hbound
  apply hinner S
  · rw [hS]
    exact (comap_mono hnorm).trans (le_normalizer_comap innerEmbedding)
  · intro h
    exact hthree (h.trans (U.card_comap_dvd_of_injective
      innerEmbedding innerEmbedding_injective))

/-- The inner normalized 3′-subgroup assertion is equivalent to exclusion of proper
3′-overgroups of a Sylow. The reverse implication uses the normalized product with that Sylow. -/
theorem inner_three_prime_iff_overgroups :
    (∀ (S : Sylow 2 He) (V : Subgroup He),
      (S : Subgroup He) ≤ normalizer (V : Set He) → ¬ 3 ∣ Nat.card V → IsPGroup 2 V) ↔
    (∀ (S : Sylow 2 He) (K : Subgroup He),
      (S : Subgroup He) ≤ K → ¬ 3 ∣ Nat.card K → K = (S : Subgroup He)) := by
  constructor
  · intro h S K hSK hthree
    exact S.3 (h S K (hSK.trans le_normalizer) hthree) hSK
  · intro h S V hnorm hthree
    have hSthree : ¬ 3 ∣ Nat.card S := by
      obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
      rw [hn]
      intro hd
      exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
    have hjoin : ¬ 3 ∣ Nat.card (V ⊔ (S : Subgroup He) : Subgroup He) := by
      intro hd
      have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes V
        (S : Subgroup He) hnorm
      have hdprod : 3 ∣ Nat.card V * Nat.card S := by
        rw [hprod]
        exact dvd_mul_of_dvd_right hd _
      exact (Nat.prime_three.dvd_mul.mp hdprod).elim hthree hSthree
    have he := h S (V ⊔ (S : Subgroup He)) le_sup_right hjoin
    exact S.isPGroup'.to_le (he ▸ le_sup_left)

end Held.LocalPairs.SylowGeometry
