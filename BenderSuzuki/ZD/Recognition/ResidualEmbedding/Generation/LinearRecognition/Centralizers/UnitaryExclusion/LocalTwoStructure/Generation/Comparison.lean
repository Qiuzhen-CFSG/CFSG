module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.Definitions
public import Theory.SpecificGroups.Suzuki.SameParameterEmbeddings
public import Theory.GroupTheory.InvariantMaximalGeneration

/-!
# Comparing a unitary factor with a recognized central quotient

The concrete PSL₂, Suzuki and PSU₃ orders at the same field parameter are
bounded by the PSU₃ order. For either actual unitary cover H, the latter
is exactly |H/Z(H)|. If H lies in a perfect group F with one of these
central quotients, its image in F/Z(F) is therefore all of that quotient.
Perfectness removes the remaining central supplement and gives H = F.

This verifies the model comparison in GLS4, Chapter 2, Lemma 13.3, without
discarding the special-unitary central kernel. The order formulas are
Huppert II.6.14 and II.10.12 and Huppert–Blackburn XI.3.3; the PSL₂
calculation follows `Theory/SpecificGroups/Suzuki/SameParameterEmbeddings`.
-/

noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion.TwoGeneratorComparison
open Subgroup Theory.GroupTheory PFAppendixIII _root_.BenderSuzuki.MatrixGroups

private def centerQuotientCongr {H K : Type*} [Group H] [Group K] (e : H ≃* K) :
    (H ⧸ center H) ≃* (K ⧸ center K) :=
  QuotientGroup.congr (center H) (center K) e (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact MulEquivClass.apply_mem_center e hx
    · intro hy
      exact ⟨e.symm y, MulEquivClass.apply_mem_center e.symm hy, e.apply_symm_apply y⟩)

private theorem eq_top_of_center_quotient_card_le
    {F : Type*} [Group F] [Finite F] (H : Subgroup F)
    (hperfect : commutator F = ⊤)
    (hcard : Nat.card (F ⧸ center F) ≤ Nat.card (H ⧸ center H)) : H = ⊤ := by
  let q := QuotientGroup.mk' (center F)
  let f := q.comp H.subtype
  have hk : f.ker ≤ center H := by
    intro x hx
    have hxC : (x : F) ∈ center F := (QuotientGroup.eq_one_iff _).mp hx
    exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp hxC y))
  have hle : Nat.card (H ⧸ center H) ≤ Nat.card f.range := by
    change (center H).index ≤ _
    rw [← index_ker]
    exact index_antitone hk
  have hr : f.range = ⊤ := by
    apply eq_top_of_card_eq
    exact le_antisymm (card_le_card_group _) (hcard.trans hle)
  have hm : H.map q = ⊤ := by
    simpa only [f, MonoidHom.range_comp, range_subtype] using hr
  have hsup : H ⊔ center F = ⊤ := by
    have he := congrArg (Subgroup.comap q) hm
    simpa only [comap_map_eq, comap_top, q, QuotientGroup.ker_mk'] using he
  have hc := commutator_eq_of_central_supplement hsup
    (show center F ≤ centralizer (⊤ : Subgroup F) from center_le_centralizer _)
  apply top_unique
  calc
    ⊤ = commutator F := hperfect.symm
    _ = ⁅H, H⁆ := hc
    _ ≤ H := commutator_le_self H

private theorem unitary_quotient_card
    {H : Type*} [Group H] [Finite H] {n : ℕ} (hn : 2 ≤ n)
    (hH : IsUnitaryCentralizerCoverAt n H) :
    Nat.card (H ⧸ center H) =
      ((2 ^ n) ^ 3 + 1) * (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) /
        Nat.gcd 3 (2 ^ n + 1) := by
  obtain ⟨E, hfield, hfinite, J, hJ, hcard, hfixed, hmodel⟩ := hH
  let : Field E := hfield
  let : Finite E := hfinite
  have hconj := External.huppert_II_10_4_conj_eq_frobenius J (2 ^ n) hcard hfixed
  have hz := HermitianForm.EvenProjectiveComparison.center_eq_bot J (by omega) hcard hconj
  have hc := Representation.SU3.BinaryDegree.card_projective J hcard hfixed
  rcases hmodel with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · let eqv := (centerQuotientCongr e).trans
      ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot)
    exact (Nat.card_congr eqv.toEquiv).trans hc
  · let eqv := (centerQuotientCongr e).trans
      ((QuotientGroup.quotientMulEquivOfEq (J.specialToProjective_ker_eq_center hz).symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective J.specialToProjective
          J.specialToProjective_surjective))
    exact (Nat.card_congr eqv.toEquiv).trans hc

private theorem psl_card (n : ℕ) (hn : n ≠ 0) :
    Nat.card (PSL2BinaryMatrixGroup n) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  let K := BinaryGaloisField n
  have hKcard : Nat.card K = 2 ^ n := by
    simpa [K, BinaryGaloisField] using GaloisField.card 2 n hn
  have hneg : (-1 : K) = 1 := CharTwo.neg_eq _
  have hcenter := External.huppert614_card_center_of_neg_one_eq_one hneg
  have hpsl := External.huppert614_card_psl_mul_center (K := K)
  rw [hcenter, hKcard] at hpsl
  simpa [K] using hpsl

private theorem order_bounds (q : ℕ) (hq : 4 ≤ q) :
    q * (q ^ 2 - 1) ≤ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1) ∧
      (q ^ 2 + 1) * q ^ 2 * (q - 1) ≤
        (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1) := by
  have hdpos : 0 < Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by decide)
  have hd : Nat.gcd 3 (q + 1) ≤ 3 := Nat.gcd_le_left _ (by decide)
  have hq2 : q ≤ q ^ 2 := Nat.le_self_pow (by decide) q
  have hq3 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
  have h3 : 3 ≤ q ^ 2 := by omega
  have hs : q - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right hq2 1
  constructor
  · apply (Nat.le_div_iff_mul_le hdpos).mpr
    calc
      q * (q ^ 2 - 1) * Nat.gcd 3 (q + 1) ≤ q * (q ^ 2 - 1) * (q ^ 2) :=
        Nat.mul_le_mul_left _ (hd.trans h3)
      _ = q ^ 3 * (q ^ 2 - 1) := by ring
      _ ≤ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) := by
        gcongr
        exact Nat.le_mul_of_pos_left _ (by positivity)
  · apply (Nat.le_div_iff_mul_le hdpos).mpr
    calc
      (q ^ 2 + 1) * q ^ 2 * (q - 1) * Nat.gcd 3 (q + 1) ≤
          (q ^ 3 + 1) * q ^ 2 * (q ^ 2 - 1) * q := by
        gcongr
        omega
      _ = (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) := by ring

private theorem bender_card_le_unitary_quotient
    {F H : Type*} [Group F] [Finite F] [Group H] [Finite H] {n : ℕ}
    (hn : 2 ≤ n) (hF : IsSimpleBenderGroupAtExponent n F)
    (hH : IsUnitaryCentralizerCoverAt n H) :
    Nat.card F ≤ Nat.card (H ⧸ center H) := by
  rw [unitary_quotient_card hn hH]
  have hq : 4 ≤ (2 : ℕ) ^ n := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
  cases hF with
  | isPSL2 he =>
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, psl_card n (by omega)]
    exact (order_bounds _ hq).1
  | isSuzuki he =>
    obtain ⟨m, rfl, ⟨e⟩⟩ := he
    rw [Nat.card_congr e.toEquiv, suzukiMatrixGroup_card m (by omega)]
    exact (order_bounds _ hq).2
  | isPSU3 he =>
    obtain ⟨E, hfield, hfinite, J, hJ, hcard, hfixed, ⟨e⟩⟩ := he
    let : Field E := hfield
    let : Finite E := hfinite
    rw [Nat.card_congr e.toEquiv, Representation.SU3.BinaryDegree.card_projective J hcard hfixed]

/-- A unitary cover at the same parameter exhausts a perfect group with a
Bender central quotient. The actual quotient by the entire unitary center
is used, retaining the special-unitary cover. -/
public theorem unitary_subgroup_eq_top_of_bender_quotient
    {F : Type*} [Group F] [Finite F] (H : Subgroup F) {n : ℕ} (hn : 2 ≤ n)
    (hperfect : commutator F = ⊤)
    (hF : IsSimpleBenderGroupAtExponent n (F ⧸ center F))
    (hH : IsUnitaryCentralizerCoverAt n H) : H = ⊤ :=
  eq_top_of_center_quotient_card_le H hperfect (bender_card_le_unitary_quotient hn hF hH)

end BenderSuzuki.ZD.UnitaryExclusion.TwoGeneratorComparison
