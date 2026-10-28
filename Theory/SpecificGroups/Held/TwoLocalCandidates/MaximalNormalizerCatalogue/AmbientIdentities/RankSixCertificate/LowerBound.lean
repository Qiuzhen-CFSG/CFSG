module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.SextetStabilizer.LowerBound
public import Theory.SpecificGroups.Held.TwoLocalCandidates.SylowContainment

/-!
# A lower bound for the literal Held max4 candidate

The square of `(a*w)^2*(a*w^2)^2`, for the max4 word `w`, has order three
and acts trivially on the six-point set. The surjective six-point action thus
contributes a divisor 135. The certified conjugate of the fixed representative
contributes 1024, yielding the lower bound 138240 by coprimality.

All word identities are checked in the original Held action. No ambient order,
maximality, or identification of an abstract group of that order is used.
Source: ATLAS HeG1-p2058B0/max4; GLS3 Table 5.3p.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.RankSixCertificate
open Subgroup LocalPairs.PairCoverage
open LocalPairs.PairCoverage.IntervalNormalizer.Inner
open LocalPairs.SylowGeometry.Calculations

private def kernelWitness : localOvergroup true :=
  let x : localOvergroup true := ⟨a, a_mem_localOvergroup true⟩
  let y : localOvergroup true := ⟨localWord true, localWord_mem_localOvergroup true⟩
  ((x * y) ^ 2 * (x * y ^ 2) ^ 2) ^ 2

private theorem kernelWitness_mem : kernelWitness ∈ (SixPoint.action true).ker := by
  change SixPoint.action true kernelWitness = 1
  simp only [kernelWitness, map_pow, map_mul, SixPoint.action_first, SixPoint.action_second]
  decide +kernel

set_option maxRecDepth 16384 in
private theorem kernelWitness_cube : kernelWitness ^ 3 = 1 := by
  apply Subtype.ext
  apply Held.eq_of_four_point_images
  decide +kernel

set_option maxRecDepth 16384 in
private theorem kernelWitness_ne_one : kernelWitness ≠ 1 := by
  have hm : representation kernelWitness.val (0 : Fin 2058) ≠ 0 := by decide +kernel
  intro he
  exact hm (congrArg (fun g : localOvergroup true => representation g.val 0) he)

private theorem oddPart_dvd_max4_card : 135 ∣ Nat.card (localOvergroup true) := by
  have hx : orderOf kernelWitness = 3 :=
    orderOf_eq_prime_iff.mpr ⟨kernelWitness_cube, kernelWitness_ne_one⟩
  have hd : 3 ∣ Nat.card (SixPoint.action true).ker :=
    hx ▸ (SixPoint.action true).ker.orderOf_dvd_natCard kernelWitness_mem
  have he := (SixPoint.action true).ker.card_mul_index
  rw [index_ker, (SixPoint.action true).range_eq_top.mpr (SixPoint.action_surjective true),
    card_top, Nat.card_perm, Nat.card_fin] at he
  have h2160 : 2160 ∣ Nat.card (localOvergroup true) := by
    rw [← he]
    exact mul_dvd_mul hd (dvd_refl 720)
  exact dvd_trans (by decide : 135 ∣ 2160) h2160

/-- The required max4 lower bound from the representative's two-group property. -/
public theorem max4_card_ge (hp : IsPGroup 2 representative) :
    138240 ≤ Nat.card (subgroup 1) := by
  have hl := InnerNormalizer.representative_card_ge_of_orbit_labels
    InnerNormalizer.orbitSizeLabel_eq_card_orbit
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have h10 : 10 ≤ n := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [← hn] using hl
  have hd : 1024 ∣ Nat.card representative := by
    rw [hn]
    exact Nat.pow_dvd_pow 2 h10
  obtain ⟨g, hg⟩ := SylowContainment.exists_conjugate_representative_le 1
  have hd2 : 1024 ∣ Nat.card (subgroup 1) := by
    have hm := card_dvd_of_le hg
    rw [card_map_of_injective (MulAut.conj g).injective] at hm
    exact hd.trans hm
  have hodd : 135 ∣ Nat.card (subgroup 1) := oddPart_dvd_max4_card
  exact Nat.le_of_dvd Nat.card_pos
    ((by decide : Nat.Coprime 1024 135).mul_dvd_of_dvd_of_dvd hd2 hodd)

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.RankSixCertificate
