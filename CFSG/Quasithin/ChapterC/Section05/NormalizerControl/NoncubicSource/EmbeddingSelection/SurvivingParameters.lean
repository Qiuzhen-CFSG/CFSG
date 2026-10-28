module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Parameters
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.PrimeRankZero
public import Theory.SpecificGroups.Janko1.Model.Certification.Order

/-!
# Parameters in the surviving small C.5.13 models

A₇ has two-rank two, and the odd center of its triple cover does not
increase two-rank. Thus a binary PSL₂ subgroup has field degree two.
For J₁ the exact order bounds the degree by three; degree three would
make 504 divide 175560. Only the required PSL₂(4) image remains.

Source: Aschbacher–Smith C.5.13, printed pp.162–163.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

theorem binary_parameter_of_surviving_containing_model (B D : Subgroup G) (hBD : B ≤ D) {n : ℕ} (hn : 1 < n)
    (hB : ClassicalGroup.IsPSL B 2 (2 ^ n))
    (hD : IsAlternating D 7 ∨ IsAlternatingCover D 7 ∨ Nonempty (D ≃* Janko1.Model)) :
    n = 2 := by
  have hnr : n ≤ primeRank 2 D := (binary_rank_lower hB).trans
    (Theory.GroupTheory.primeRank_le_of_injective 2 (inclusion hBD) (inclusion_injective hBD))
  rcases hD with hAlt | hCover | hJ
  · obtain ⟨e⟩ := hAlt
    rw [primeRank_equiv 2 e,
      Representation.AlternatingSevenConjugatePair.ElementaryGeometry.primeRank_alternating] at hnr
    omega
  · obtain ⟨_, ⟨z⟩, ⟨e⟩⟩ := hCover
    have hz : primeRank 2 (center D) = 0 :=
      PrimeRank.eq_zero_iff_not_dvd_card.mpr (by rw [Nat.card_congr z.toEquiv]; norm_num)
    have hr := primeRank_le_ker_add (p := 2) (QuotientGroup.mk' (center D))
    rw [QuotientGroup.ker_mk', hz, zero_add, primeRank_equiv 2 e,
      Representation.AlternatingSevenConjugatePair.ElementaryGeometry.primeRank_alternating] at hr
    omega
  · obtain ⟨e⟩ := hJ
    have hd : 2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ 175560 := by
      rw [← binary_card hB, ← Janko1.card_model, ← Nat.card_congr e.toEquiv]
      exact card_dvd_of_injective (inclusion hBD) (inclusion_injective hBD)
    have hnle : n ≤ 3 := by
      have htwo : 2 ^ n ∣ 175560 := (dvd_mul_right _ _).trans hd
      have hh := (Nat.prime_two.pow_dvd_iff_le_factorization (by decide : 175560 ≠ 0)).mp htwo
      have hv : Nat.factorization 175560 2 = 3 := by
        rw [show 175560 = 2 ^ 3 * 21945 by decide,
          Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
          Nat.factorization_pow_self Nat.prime_two,
          Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 21945)]
      rwa [hv] at hh
    have hc : n = 2 ∨ n = 3 := by omega
    rcases hc with rfl | rfl
    · rfl
    · norm_num at hd
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
