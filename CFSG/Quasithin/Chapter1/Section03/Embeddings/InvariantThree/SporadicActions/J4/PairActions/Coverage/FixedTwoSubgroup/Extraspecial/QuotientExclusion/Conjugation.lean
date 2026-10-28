module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.Reduction

/-!
# Conjugation and the large radical normalizer quotients of J₄

Conjugation gives the actual map N(K) → Aut(K), with kernel C(K).
If 3 does not divide the kernel order and 27 does not divide the image
order, then 27 does not divide |N(K)|. Lagrange's theorem excludes every
subgroup of N(K)/K whose order is a multiple of 27.

The two concrete bounds below are separate proof obligations. In particular,
the image is the image of the ambient model normalizer, not an assumed
abstract local group. The index lemma reduces the input range to six powers
of two without classifying any normalizers.

Source context: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), using Aschbacher, *Overgroups of Sylow
subgroups in sporadic groups* (1986). This module proves the transfer
argument, not the cited model calculation.
-/

@[expose] public section

open Subgroup
open Janko4.OuterReduction.OddIndex

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

/-- The ambient centralizer bound needed by the conjugation route.
All restrictions on K are the inputs of the original quotient problem. -/
def FixedTwoLargeCentralizerThreeFree : Prop :=
  ∀ [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (S : Sylow 2 Janko4.Model), (S : Subgroup Janko4.Model) = twoSubgroup →
    ∀ K : Subgroup Janko4.Model, K ≤ twoSubgroup →
      twoSubgroup ≤ normalizer (K : Set Janko4.Model) →
      K.relIndex twoSubgroup ≤ 32 → K.IsPRadical 2 →
      ¬ 3 ∣ Nat.card (centralizer (K : Set Janko4.Model))

/-- The required bound concerns automorphisms actually induced by N_Model(K).
A bound on the full automorphism group would suffice, but is not required. -/
def FixedTwoLargeConjugationThreePartBound : Prop :=
  ∀ [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (S : Sylow 2 Janko4.Model), (S : Subgroup Janko4.Model) = twoSubgroup →
    ∀ K : Subgroup Janko4.Model, K ≤ twoSubgroup →
      twoSubgroup ≤ normalizer (K : Set Janko4.Model) →
      K.relIndex twoSubgroup ≤ 32 → K.IsPRadical 2 →
      ¬ 27 ∣ Nat.card K.normalizerMonoidHom.range

/-- Kernel and image orders of the actual conjugation map control the
three-part of the ambient normalizer. -/
theorem fixedTwoLargeNormalizer_not_dvd_twentySeven_of_conjugation
    {K : Subgroup Janko4.Model}
    (hcentral : ¬ 3 ∣ Nat.card (centralizer (K : Set Janko4.Model)))
    (haction : ¬ 27 ∣ Nat.card K.normalizerMonoidHom.range) :
    ¬ 27 ∣ Nat.card (normalizer (K : Set Janko4.Model)) := by
  let f := K.normalizerMonoidHom
  have hker : Nat.card f.ker = Nat.card (centralizer (K : Set Janko4.Model)) := by
    rw [normalizerMonoidHom_ker,
      Nat.card_congr
        (subgroupOfEquivOfLe (centralizer_le_normalizer (K : Set Janko4.Model))).toEquiv]
  have hcop : Nat.Coprime 27 (Nat.card f.ker) := by
    rw [hker]
    exact ((Nat.prime_three.coprime_iff_not_dvd).mpr hcentral).pow_left 3
  have hmul : Nat.card f.ker * Nat.card f.range =
      Nat.card (normalizer (K : Set Janko4.Model)) := by
    rw [← index_ker]
    exact f.ker.card_mul_index
  intro hd
  exact haction (hcop.dvd_of_dvd_mul_left (hmul ▸ hd))

/-- Lagrange's theorem applies through the actual quotient N_Model(K)/K.
The two concrete bounds exclude all multiples of 27, without extra
conditions on the subgroup of the quotient. -/
theorem fixedTwoLargeNormalizerQuotient_card_ne_of_conjugation
    {K : Subgroup Janko4.Model}
    (hcentral : ¬ 3 ∣ Nat.card (centralizer (K : Set Janko4.Model)))
    (haction : ¬ 27 ∣ Nat.card K.normalizerMonoidHom.range)
    (L : Subgroup (FixedTwoLargeNormalizerQuotient K)) (n : ℕ) :
    Nat.card L ≠ 27 * n := by
  intro hcard
  apply fixedTwoLargeNormalizer_not_dvd_twentySeven_of_conjugation hcentral haction
  exact (show 27 ∣ Nat.card L by rw [hcard]; exact dvd_mul_right _ _).trans
    (L.card_subgroup_dvd_card.trans
      (card_quotient_dvd_card (K.subgroupOf (normalizer (K : Set Janko4.Model)))))

/-- An abstract automorphism bound can be used only after restricting to
the image of the actual ambient conjugation map. -/
theorem fixedTwoLargeConjugation_not_dvd_twentySeven_of_aut
    {K : Subgroup Janko4.Model} (haut : ¬ 27 ∣ Nat.card (MulAut K)) :
    ¬ 27 ∣ Nat.card K.normalizerMonoidHom.range := by
  intro hd
  exact haut (hd.trans K.normalizerMonoidHom.range.card_subgroup_dvd_card)

/-- The specified relative-index bound permits exactly the exponents 0–5.
This uses the certified order of the actual fixed two-subgroup. -/
theorem fixedTwoLargeIndex_eq_pow_two (K : Subgroup Janko4.Model)
    (hindex : K.relIndex twoSubgroup ≤ 32) :
    ∃ n ≤ 5, K.relIndex twoSubgroup = 2 ^ n := by
  have hd := K.relIndex_dvd_card twoSubgroup
  rw [twoSubgroup_card] at hd
  obtain ⟨n, _, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  refine ⟨n, ?_, hn⟩
  by_contra! hh
  have hlarge := Nat.pow_le_pow_right (by decide : 0 < 2) hh
  rw [← hn] at hlarge
  norm_num at hlarge
  omega

/-- Every candidate for the quotient problem has order at least 2¹⁶,
independently of how it arose from a source pair. -/
theorem fixedTwoLargeSubgroup_card_ge {K : Subgroup Janko4.Model}
    (hKT : K ≤ twoSubgroup) (hindex : K.relIndex twoSubgroup ≤ 32) :
    2 ^ 16 ≤ Nat.card K := by
  have hmul : Nat.card K * K.relIndex twoSubgroup = 2 ^ 21 := by
    have hc := (K.subgroupOf twoSubgroup).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hKT).toEquiv, twoSubgroup_card] at hc
    exact hc
  have hle := Nat.mul_le_mul_left (Nat.card K) hindex
  rw [hmul] at hle
  norm_num at hle ⊢
  omega

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
