module
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.Geometry
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.SixPoint
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.TwoGroup
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer
public import Theory.SpecificGroups.Held.Model.FourPointBase

/-!
# A lower bound for the literal max3 subgroup

The word `(a * localWord false)^5` is a nonidentity element of order three
in the kernel of the established surjective six-point action. Thus 135 divides
the local subgroup order. The permitted orbit certificate for the existing
representative supplies a two-subgroup of order at least 1024. Lagrange's theorem
and coprimality give the lower bound 138240.

The representative orbit identity remains an explicit allowed premise. No Held
order, simplicity, maximal-subgroup catalogue, or extension shape is assumed.
Source: ATLAS HeG1-p2058B0/max3; GLS3 Table 5.3p.
-/

public section
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3
open Subgroup
open Held.LocalPairs.SylowGeometry.Calculations

private def kernelWitness : localOvergroup false :=
  (⟨a, a_mem_localOvergroup false⟩ *
    ⟨localWord false, PairCoverage.localWord_mem_localOvergroup false⟩) ^ 5

private theorem kernelWitness_mem : kernelWitness ∈ (SixPoint.action false).ker := by
  change SixPoint.action false kernelWitness = 1
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
  exact hm (congrArg (fun g : localOvergroup false => representation g.val 0) he)

set_option maxRecDepth 16384 in
theorem oddPart_dvd_local_card : 135 ∣ Nat.card (localOvergroup false) := by
  have hx : orderOf kernelWitness = 3 :=
    orderOf_eq_prime_iff.mpr ⟨kernelWitness_cube, kernelWitness_ne_one⟩
  have hd : 3 ∣ Nat.card (SixPoint.action false).ker :=
    hx ▸ (SixPoint.action false).ker.orderOf_dvd_natCard kernelWitness_mem
  have he := (SixPoint.action false).ker.card_mul_index
  rw [index_ker, (SixPoint.action false).range_eq_top.mpr (SixPoint.action_surjective false),
    card_top, Nat.card_perm, Nat.card_fin] at he
  have h2160 : 2160 ∣ Nat.card (localOvergroup false) := by
    rw [← he]
    exact mul_dvd_mul hd (dvd_refl 720)
  exact dvd_trans (by decide : 135 ∣ 2160) h2160

theorem local_card_ge_of_representative_orbits
    (horbits : ∀ x : Fin 2058,
      InnerNormalizer.orbitSizeLabel x = Nat.card (MulAction.orbit representative x)) :
    138240 ≤ Nat.card (localOvergroup false) := by
  have hp := InnerNormalizer.representative_card_ge_of_orbit_labels horbits
  obtain ⟨n, hn⟩ := representative_isPGroup.exists_card_eq
  have h10 : 10 ≤ n := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [← hn] using hp
  have hd2 : 1024 ∣ Nat.card (localOvergroup false) :=
    (show 1024 ∣ Nat.card representative by rw [hn]; exact Nat.pow_dvd_pow 2 h10).trans
      (card_dvd_of_le representative_le_localOvergroup)
  have hd : 138240 ∣ Nat.card (localOvergroup false) :=
    (by decide : Nat.Coprime 1024 135).mul_dvd_of_dvd_of_dvd hd2 oddPart_dvd_local_card
  exact Nat.le_of_dvd (Finite.card_pos) hd

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3
