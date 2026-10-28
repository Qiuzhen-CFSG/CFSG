module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface

/-!
# The exceptional C.2.7 rows exclude an A₆ section

The embedded A₆ section forces a factor of five in the intersection.
The exceptional indices 15 and 35 would then force a factor of 25 in K.
But their actual two-core quotients have orders 1080 and 2520, respectively,
and the two-core cannot supply the extra factor of five. The triple-cover
calculation retains its center of order three and its actual A₆ quotient.

Source: Aschbacher--Smith C.2.7(3)(c)--(d), pp.145--147, and the comparison
in 3.3.22, p.597. The fixed-coset applications are in
SourceAlternatingSeven/LocalAnalysisSylowResidualsComponentsExclusions.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {H K R M B : Subgroup G}

omit [Finite G] in
private theorem twentyFive_dvd_of_six_index
    (hB : B ≤ M ⊓ K)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (hi : 5 ∣ ((M ⊓ K).subgroupOf K).index) : 25 ∣ Nat.card K := by
  have h5 : 5 ∣ Nat.card B := by
    have hd := card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 B))
      (QuotientGroup.mk'_surjective _)
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hd
    exact (by decide : 5 ∣ 360).trans hd
  have hd : 5 ∣ Nat.card ((M ⊓ K).subgroupOf K) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show M ⊓ K ≤ K from inf_le_right)).toEquiv]
    exact h5.trans (card_dvd_of_le hB)
  simpa only [show 5 * 5 = 25 by decide, card_mul_index] using Nat.mul_dvd_mul hd hi

private theorem not_twentyFive_dvd_of_core_quotient_card
    (hcard : Nat.card (K ⧸ pCore 2 K) = 1080 ∨
      Nat.card (K ⧸ pCore 2 K) = 2520) : ¬ 25 ∣ Nat.card K := by
  obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_eq
  have he : Nat.card K = 2 ^ k * Nat.card (K ⧸ pCore 2 K) := by
    rw [← (pCore 2 K).card_mul_index, hk, index_eq_card]
  rw [he]
  intro hd
  have hc : Nat.Coprime 25 (2 ^ k) := (by decide : Nat.Coprime 25 2).pow_right k
  have hd' := hc.dvd_of_dvd_mul_left hd
  rcases hcard with hh | hh <;> rw [hh] at hd' <;> norm_num at hd'

/-- C.2.7(3)(c) cannot contain the original A6 residual. -/
theorem no_ahatSix_alternative_of_six
    (hB : B ≤ M ⊓ K)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (hm : IsExceptionalAhat6Block K)
    (hi : ((M ⊓ K).subgroupOf K).index = 15) : False := by
  have hd := twentyFive_dvd_of_six_index hB e (by rw [hi]; decide)
  apply not_twentyFive_dvd_of_core_quotient_card (Or.inl ?_) hd
  obtain ⟨eK⟩ := hm.2.2.2.1
  calc
    Nat.card (K ⧸ pCore 2 K) =
        Nat.card (center (K ⧸ pCore 2 K)) *
          Nat.card ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) := by
      rw [← (center (K ⧸ pCore 2 K)).index_eq_card, card_mul_index]
    _ = 1080 := by
      rw [hm.2.2.1, Nat.card_congr eK.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.factorial]

/-- C.2.7(3)(d) cannot contain the original A6 residual. -/
theorem no_exceptionalSeven_alternative_of_six
    (hB : B ≤ M ⊓ K)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (hm : IsExceptionalA7Block K)
    (hi : ((M ⊓ K).subgroupOf K).index = 35) : False := by
  have hd := twentyFive_dvd_of_six_index hB e (by rw [hi]; decide)
  apply not_twentyFive_dvd_of_core_quotient_card (Or.inr ?_) hd
  obtain ⟨eK⟩ := hm.2.1
  rw [Nat.card_congr eK.toEquiv, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

end CFSG.Quasithin.ChapterC.C27Source
