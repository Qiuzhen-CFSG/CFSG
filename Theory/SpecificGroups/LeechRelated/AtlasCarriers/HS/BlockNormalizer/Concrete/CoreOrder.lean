module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.Action

/-!
# The order of the actual HS normalizer two-core

The surjective conjugation action on the characteristic elementary eight
has kernel O₂(M), and quotient of order 168. The certified Sylow subgroup
of order 512 is contained in M. Comparing these orders with the order of
the exact HS carrier forces |O₂(M)| = 64. No abelian structure or abstract
shape label is used in this count.

Source: Aschbacher–Smith I.2.2(5), final HS paragraph, printed p.412;
GLS3 Table 5.3m. The central double-cover application is HSLocal.NormalizerModule.
-/

public section
open Subgroup
namespace Sporadic.LeechRelated.HS.BlockNormalizer

/-- The model core is the kernel of its actual action on the elementary eight. -/
theorem model_core_eq_action_ker :
    pCore 2 baseNormalizer = baseElementary.normalizerMonoidHom.ker :=
  (baseNormalizer_ker_eq_pCore_of_surjective baseNormalizer_action_surjective).symm

/-- The actual model normalizer has core order 64. -/
theorem model_core_card : Nat.card (pCore 2 baseNormalizer) = 64 := by
  obtain ⟨f⟩ := baseNormalizer_quotient_of_surjective baseNormalizer_action_surjective
  have hi : (pCore 2 baseNormalizer).index = 168 :=
    (Nat.card_congr f.toEquiv).trans Matrix.PSL3Two.card_SL
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := baseNormalizer)).exists_card_eq
  have hc : Nat.card baseNormalizer = 2 ^ n * 168 := by
    rw [← (pCore 2 baseNormalizer).card_mul_index, hn, hi]
  have h512 : 512 ∣ 2 ^ n * 168 := by
    have h := Subgroup.card_dvd_of_le baseSylow_le_normalizer
    change Nat.card Sporadic.LeechRelated.HS.EvenLocalCandidates.subgroup ∣
      Nat.card baseNormalizer at h
    rwa [Sporadic.LeechRelated.HS.EvenLocalCandidates.subgroup_card, hc] at h
  have hbig : 2 ^ n * 168 ∣ 44352000 := by
    have h := baseNormalizer.card_subgroup_dvd_card
    rwa [hc, Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier] at h
  have hn6 : n ≤ 6 := by
    by_contra hn6
    have hd : 2 ^ 7 * 168 ∣ 2 ^ n * 168 :=
      Nat.mul_dvd_mul_right (pow_dvd_pow 2 (by omega)) 168
    have hbad := hd.trans hbig
    norm_num at hbad
  rw [hn]
  interval_cases n <;> omega

end Sporadic.LeechRelated.HS.BlockNormalizer
