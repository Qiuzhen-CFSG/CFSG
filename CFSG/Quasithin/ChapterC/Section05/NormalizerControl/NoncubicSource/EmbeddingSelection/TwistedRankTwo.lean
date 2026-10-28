module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Parameters
public import Theory.SpecificGroups.Triality.StandardTwoRank.Sylow
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound

/-!
# The twisted rank-two cases of the original C.5.13 sieve

The faithful full Sylow acting on PSL₂(2ⁿ) has order dividing 2ⁿn. If a
containing group has two-rank at most r and order divisible by 2^(2r),
then n ≤ r contradicts this Sylow bound. Genuine triality has two-rank
5m and a subgroup of order 2^(12m); the elementary-subgroup theorem for
Ree supplies the same comparison with m replaced by 2m+1.

The original full Sylow, inclusion, normalization and faithful action are
retained. No parabolic or whole-Borel placement is assumed.
Source: Aschbacher–Smith C.5.13, printed pp.162–163, using the earlier
rank-two catalogue; GLS3, Lemma 3.3.9 for the Ree elementary bound.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
variable {G : Type*} [Group G] [Finite G]

/-- A containing group with a sufficiently large Sylow order cannot contain
the binary image normalized faithfully by the full source Sylow. -/
theorem not_binary_containing_of_rank_order_bound
    (T : Sylow 2 G) (B L : Subgroup G) {n r : ℕ} (hn : 0 < n)
    (hB : ClassicalGroup.IsPSL B 2 (2 ^ n)) (hBL : B ≤ L)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hfaith : (T : Subgroup G) ⊓ centralizer (B : Set G) = ⊥)
    (hr : primeRank 2 L ≤ r) (hd : 2 ^ (2 * r) ∣ Nat.card L) : False := by
  have hnr : n ≤ r := (binary_rank_lower hB).trans
    ((Theory.GroupTheory.primeRank_le_of_injective 2 (inclusion hBL) (inclusion_injective hBL)).trans hr)
  have hT : 2 ^ (2 * r) ∣ Nat.card T :=
    T.pow_dvd_card_of_pow_dvd_card (hd.trans L.card_subgroup_dvd_card)
  have hbound : 2 ^ (2 * r) ≤ 2 ^ n * n :=
    Nat.le_of_dvd (by positivity) (hT.trans (binary_normalizer_card_dvd T B hn hB hTB hfaith))
  have hsmall : 2 ^ n * n < 2 ^ (2 * r) := calc
    2 ^ n * n < 2 ^ n * 2 ^ n := Nat.mul_lt_mul_of_pos_left n.lt_two_pow_self (by positivity)
    _ = 2 ^ (n + n) := (pow_add _ _ _).symm
    _ ≤ 2 ^ (2 * r) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- The genuine binary triality containing-model case is impossible. -/
theorem not_triality_containing
    (T : Sylow 2 G) (B L : Subgroup G) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hB : ClassicalGroup.IsPSL B 2 (2 ^ n)) (hBL : B ≤ L)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hfaith : (T : Subgroup G) ⊓ centralizer (B : Set G) = ⊥) :
    ¬ Triality.Standard.IsTrialityGroupAt (2 ^ m) L := by
  intro hL
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff L m hm).mp hL
  have hr : primeRank 2 L ≤ 5 * m := by
    rw [primeRank_equiv 2 e]
    exact Triality.Standard.TwoRank.twoRank_le_five_mul m hm
  have hd : 2 ^ (12 * m) ∣ Nat.card L := by
    rw [Nat.card_congr e.toEquiv]
    have h := (Triality.Standard.Parabolics.unipotent (Triality.Standard.binaryParameters m hm)).card_subgroup_dvd_card
    rw [Triality.Standard.Parabolics.card_unipotent_binary _ rfl] at h
    simpa only [Triality.Standard.binaryParameters_q, ← pow_mul, Nat.mul_comm m 12] using h
  exact not_binary_containing_of_rank_order_bound T B L hn hB hBL hTB hfaith hr
    ((pow_dvd_pow 2 (by omega : 2 * (5 * m) ≤ 12 * m)).trans hd)
/-- The genuine Ree containing-model case is impossible in the simple range. -/
theorem not_ree_containing
    (T : Sylow 2 G) (B L : Subgroup G) {n m : ℕ} (hn : 0 < n) (hm : 1 ≤ m)
    (hB : ClassicalGroup.IsPSL B 2 (2 ^ n)) (hBL : B ≤ L)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hfaith : (T : Subgroup G) ⊓ centralizer (B : Set G) = ⊥) :
    ¬ Chapter1.Section02.LocalModels.IsReeF4At L m := by
  rintro ⟨d, ⟨e⟩⟩
  let f := e.trans d.modelEquiv
  have hr : primeRank 2 L ≤ 5 * (2 * m + 1) := by
    rw [primeRank_equiv 2 f]
    exact (primeRank_le_iff_elementary_card_le _).mpr (ReeF4.ElementaryTwoBound.card_le m hm)
  have hd : 2 ^ (12 * (2 * m + 1)) ∣ Nat.card L := by
    rw [Nat.card_congr f.toEquiv, ← ReeF4.AutomorphismTwoRank.sylow_card m]
    exact (ReeF4.AutomorphismTwoRank.sylow m : Subgroup (ReeF4.Model m)).card_subgroup_dvd_card
  exact not_binary_containing_of_rank_order_bound T B L hn hB hBL hTB hfaith hr
    ((pow_dvd_pow 2 (by omega : 2 * (5 * (2 * m + 1)) ≤ 12 * (2 * m + 1))).trans hd)
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
