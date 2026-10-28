module

public import Theory.SpecificGroups.Rudvalis.Model.TwoRankSix.Checks
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.NormalFormCoverage
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.GroupTheory.PrimeRankElementary

/-!
# Intrinsic two-rank of the concrete Rudvalis group

Every elementary abelian two-subgroup of the fixed word-defined Sylow subgroup
injects into 64 labels: the square check places each of its elements in the
labelled table, and the separation check distinguishes commuting elements of
one label. No relative normality or elementary-subgroup classification is used.
Sylow conjugacy and the elementary-cardinality criterion then bound the prime
rank of the original degree-4060 permutation group by six.

Source: Guralnick--Malle, Proposition 5.1, Ru paragraph, manuscript p.17;
GLS3, Section 5.6, printed p.307. This is a finite certificate proof of the
upper bound used there. The original carrier, word coordinates and action
convention are preserved; see `TwoRankSix/source/README.md`.
-/

open scoped IsMulCommutative

namespace Rudvalis.TwoRankSix
open SylowOvergroups.RadicalCoverage.SylowCertificate
open SylowOvergroups.RadicalCoverage.SylowCertificate.LocalOrder

private theorem square_fixed (n : Fin 16384) (h : candidateNormalForm n ^ 2 = 1)
    (x : Fin 4060) : normalMap n (normalMap n x) = x := by
  calc
    _ = candidateNormalForm n ^ 2 • x := by
      rw [pow_two, mul_smul, normal_smul, normal_smul]
    _ = x := by rw [h, one_smul]

/-- A normal form squaring to one occurs at its declared table address. -/
public theorem entry_of_square_eq_one (n : Fin 16384)
    (h : candidateNormalForm n ^ 2 = 1) : entry (label n) (slot n) = n := by
  rcases covered n with he | h0 | h1
  · exact he
  · exact (h0 (square_fixed n h 0)).elim
  · exact (h1 (square_fixed n h 1)).elim

/-- Commuting normal forms squaring to one are distinguished by their labels. -/
public theorem index_eq_of_commute_of_label_eq (m n : Fin 16384)
    (hm : candidateNormalForm m ^ 2 = 1) (hn : candidateNormalForm n ^ 2 = 1)
    (hc : Commute (candidateNormalForm m) (candidateNormalForm n))
    (hl : label m = label n) : m = n := by
  have hx (x : Fin 4060) : normalMap m (normalMap n x) = normalMap n (normalMap m x) := by
    calc
      _ = (candidateNormalForm m * candidateNormalForm n) • x := by
        rw [mul_smul, normal_smul, normal_smul]
      _ = (candidateNormalForm n * candidateNormalForm m) • x :=
        congrArg (fun g : Model => g • x) hc.eq
      _ = _ := by rw [mul_smul, normal_smul, normal_smul]
  have hs := separated (label m) (slot m) (slot n)
  change entry (label m) (slot m) = entry (label m) (slot n) ∨ _ ∨ _ at hs
  rw [entry_of_square_eq_one m hm, hl, entry_of_square_eq_one n hn] at hs
  rcases hs with he | h0 | h1
  · exact he
  · exact (h0 (hx 0)).elim
  · exact (h1 (hx 1)).elim

/-- Every elementary two-subgroup of the concrete candidate has order at most 64.
The subgroup need not be normal in the candidate or in the ambient group. -/
public theorem candidate_elementary_card_le (E : Subgroup Model) (hE : E ≤ candidate)
    [IsElementaryAbelian 2 E] : Nat.card E ≤ 64 := by
  classical
  let n : E → Fin 16384 := fun x =>
    Classical.choose (exists_candidateNormalForm (hE x.property))
  have hn (x : E) : candidateNormalForm (n x) = (x : Model) :=
    Classical.choose_spec (exists_candidateNormalForm (hE x.property))
  have hf : Function.Injective (fun x : E => label (n x)) := by
    intro x y hxy
    apply Subtype.ext
    have he := index_eq_of_commute_of_label_eq (n x) (n y)
      (by rw [hn]; exact elemPow_eq_one_of_isElementaryAbelian _ x.property)
      (by rw [hn]; exact elemPow_eq_one_of_isElementaryAbelian _ y.property)
      (by rw [hn, hn]; exact setLike_mul_comm x.property y.property) hxy
    rw [← hn x, ← hn y, he]
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective _ hf

/-- The labelled point certificate bounds the intrinsic rank of the candidate. -/
public theorem candidate_primeRank_le_six : primeRank 2 candidate ≤ 6 := by
  apply (primeRank_le_iff_elementary_card_le candidate).mpr
  intro E hE
  let := hE
  let : IsElementaryAbelian 2 (E.map candidate.subtype) :=
    IsElementaryAbelian.map candidate.subtype
  have hc := candidate_elementary_card_le (E.map candidate.subtype) (by
    rintro x ⟨y, _, rfl⟩
    exact y.property)
  rwa [Subgroup.card_map_of_injective candidate.subtype_injective] at hc

private theorem candidate_index_odd : ¬ 2 ∣ candidate.index := by
  intro hi
  apply not_two_pow_fifteen_dvd_card_model
  rw [← candidate.card_mul_index, candidate_card]
  exact Nat.mul_dvd_mul_left 16384 hi

end Rudvalis.TwoRankSix

namespace Rudvalis
open SylowOvergroups.RadicalCoverage.SylowCertificate

/-- The actual degree-4060 Rudvalis permutation group has two-rank at most six.
This discharges the intrinsic rank premise of the Ru normalizer exclusion in
Guralnick--Malle Proposition 5.1 without simplicity or perfectness assumptions. -/
public theorem primeRank_le_six : primeRank 2 Model ≤ 6 := by
  let S : Sylow 2 Model := LocalOrder.candidate_isTwoGroup.toSylow
    TwoRankSix.candidate_index_odd
  calc
    primeRank 2 Model = primeRank 2 S := S.primeRank_eq
    _ ≤ 6 := TwoRankSix.candidate_primeRank_le_six

end Rudvalis
