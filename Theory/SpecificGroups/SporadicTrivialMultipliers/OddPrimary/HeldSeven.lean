module
public import Theory.SpecificGroups.SporadicTrivialMultipliers.OddPrimary.HeldBounds
public import Theory.SpecificGroups.SporadicTrivialMultipliers.OddPrimary.ScaledPair
public import Theory.SpecificGroups.Held.OddCubeCandidates.Cardinality
public import Theory.SpecificGroups.Held.Model.FourPointBase
public import Theory.GroupTheory.PGroup.ExtraspecialPrimeCube

/-!
# Seven-primary kernels over Held

Two explicit words in the existing order-343 subgroup generate that same
subgroup, as certified by reverse expressions for its original generators.
The displayed ambient word scales them by 2 and 4 and fixes their commutator.
The checks use the actual four-point base and compact permutation tables.
The scaled-pair transfer excludes seven from every finite perfect central
kernel; the proved odd-order bound supplies actual Sylow status.

The ambient word was extracted from the full normalizer using GAP's
PreImagesRepresentative and then independently checked by the Lean kernel.
No normalizer-order or external group-recognition claim is used.
Source: Aschbacher–Smith I.1.3, printed p.407; ATLAS HeG1-p2058B0 and the
existing HeG1-max6W1 subgroup words.
-/

open Subgroup
open scoped commutatorElement
namespace Held.OddPrimary
open OddCubeCandidates CardinalityCertificates
private def sevenActor : He :=
  (a * b * a * b * a * b⁻¹ * a * b *
    a * b⁻¹ * a * b ^ (-2 : ℤ) * a * b * a * b *
    a * b⁻¹ * a * b ^ (-2 : ℤ) * a * b ^ (2 : ℤ) * a * b *
    a * b ^ (-2 : ℤ) * a * b⁻¹ * a * b * a * b⁻¹ *
    a * b * a * b ^ (2 : ℤ) * a * b * a⁻¹ * b *
    a⁻¹ * b⁻¹ * a⁻¹ * b ^ (-4 : ℤ) * a⁻¹ * b ^ (2 : ℤ) * a * b ^ (-2 : ℤ) *
    a * b ^ (2 : ℤ) * a * b ^ (-2 : ℤ) * a * b ^ (2 : ℤ) * a)⁻¹
private def sevenEigenFirst : He := sevenSecond⁻¹ * sevenFirst * sevenSecond ^ 3
private def sevenEigenSecond : He :=
  sevenSecond * sevenFirst ^ (-2 : ℤ) * sevenSecond ^ (-2 : ℤ) * sevenFirst ^ 2

private theorem seven_first_mem : sevenEigenFirst ∈ seven := by
  exact mul_mem (mul_mem (inv_mem sevenSecond_mem) sevenFirst_mem) (pow_mem sevenSecond_mem _)
private theorem seven_second_mem : sevenEigenSecond ∈ seven := by
  exact mul_mem (mul_mem (mul_mem sevenSecond_mem (zpow_mem sevenFirst_mem _))
    (zpow_mem sevenSecond_mem _)) (pow_mem sevenFirst_mem _)
private theorem seven_back_first :
    sevenFirst = sevenEigenFirst ^ 2 * sevenEigenSecond ^ 2 * sevenEigenFirst⁻¹ := by
  apply eq_of_four_point_images
  simp only [sevenEigenFirst, sevenEigenSecond, map_mul, map_inv, map_pow, map_zpow]
  rw [← sevenX_eq, ← sevenY_eq]
  decide +kernel
private theorem seven_back_second :
    sevenSecond = sevenEigenFirst ^ (-3 : ℤ) * sevenEigenSecond⁻¹ * sevenEigenFirst ^ 3 := by
  apply eq_of_four_point_images
  simp only [sevenEigenFirst, sevenEigenSecond, map_mul, map_inv, map_pow, map_zpow]
  rw [← sevenX_eq, ← sevenY_eq]
  decide +kernel
private theorem seven_pair_generates :
    closure ({sevenEigenFirst, sevenEigenSecond} : Set He) = seven := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro x hx
    rcases (show x = sevenEigenFirst ∨ x = sevenEigenSecond by simpa using hx) with rfl | rfl
    · exact seven_first_mem
    · exact seven_second_mem
  · apply (closure_le _).mpr
    let P := closure ({sevenEigenFirst, sevenEigenSecond} : Set He)
    have hx : sevenEigenFirst ∈ P := subset_closure (by simp)
    have hy : sevenEigenSecond ∈ P := subset_closure (by simp)
    intro x he
    rcases (show x = sevenFirst ∨ x = sevenSecond by simpa using he) with rfl | rfl
    · rw [seven_back_first]
      exact mul_mem (mul_mem (pow_mem hx _) (pow_mem hy _)) (inv_mem hx)
    · rw [seven_back_second]
      exact mul_mem (mul_mem (zpow_mem hx _) (inv_mem hy)) (pow_mem hx _)
private theorem seven_first_pow : sevenEigenFirst ^ 7 = 1 := by
  apply eq_of_four_point_images
  simp only [sevenEigenFirst, map_pow, map_mul, map_inv, map_one]
  rw [← sevenX_eq, ← sevenY_eq]
  decide +kernel
private theorem seven_second_pow : sevenEigenSecond ^ 7 = 1 := by
  apply eq_of_four_point_images
  simp only [sevenEigenSecond, map_pow, map_zpow, map_mul, map_one]
  rw [← sevenX_eq, ← sevenY_eq]
  decide +kernel
private theorem seven_first_comm : Commute sevenEigenFirst ⁅sevenEigenFirst, sevenEigenSecond⁆ := by
  change sevenEigenFirst * ⁅sevenEigenFirst, sevenEigenSecond⁆ = ⁅sevenEigenFirst, sevenEigenSecond⁆ * sevenEigenFirst
  apply eq_of_four_point_images
  simp only [commutatorElement_def, sevenEigenFirst, sevenEigenSecond, map_mul, map_inv, map_pow, map_zpow]
  rw [← sevenX_eq, ← sevenY_eq]
  decide +kernel
private theorem seven_second_comm : Commute sevenEigenSecond ⁅sevenEigenFirst, sevenEigenSecond⁆ := by
  change sevenEigenSecond * ⁅sevenEigenFirst, sevenEigenSecond⁆ = ⁅sevenEigenFirst, sevenEigenSecond⁆ * sevenEigenSecond
  apply eq_of_four_point_images
  simp only [commutatorElement_def, sevenEigenFirst, sevenEigenSecond, map_mul, map_inv, map_pow, map_zpow]
  rw [← sevenX_eq, ← sevenY_eq]
  decide +kernel
private theorem seven_commutator_ne : ⁅sevenEigenFirst, sevenEigenSecond⁆ ≠ 1 := by
  have hn : representation (sevenEigenFirst * sevenEigenSecond) 0 ≠
      representation (sevenEigenSecond * sevenEigenFirst) 0 := by
    simp only [sevenEigenFirst, sevenEigenSecond, map_mul, map_inv, map_pow, map_zpow]
    rw [← sevenX_eq, ← sevenY_eq]
    decide +kernel
  intro h
  exact hn (congrArg (fun g : He => representation g 0)
    (commutatorElement_eq_one_iff_mul_comm.mp h))
private theorem seven_actor_first :
    sevenActor * sevenEigenFirst * sevenActor⁻¹ = sevenEigenFirst ^ 2 := by
  apply eq_of_four_point_images
  simp only [sevenEigenFirst, map_mul, map_inv, map_pow]
  rw [← sevenX_eq, ← sevenY_eq]
  decide +kernel
private theorem seven_actor_second :
    sevenActor * sevenEigenSecond * sevenActor⁻¹ = sevenEigenSecond ^ 4 := by
  apply eq_of_four_point_images
  simp only [sevenEigenSecond, map_mul, map_inv, map_pow, map_zpow]
  rw [← sevenX_eq, ← sevenY_eq]
  decide +kernel
private theorem seven_actor_comm : Commute sevenActor ⁅sevenEigenFirst, sevenEigenSecond⁆ := by
  change sevenActor * ⁅sevenEigenFirst, sevenEigenSecond⁆ = ⁅sevenEigenFirst, sevenEigenSecond⁆ * sevenActor
  apply eq_of_four_point_images
  simp only [commutatorElement_def, sevenEigenFirst, sevenEigenSecond, map_mul, map_inv, map_pow, map_zpow]
  rw [← sevenX_eq, ← sevenY_eq]
  decide +kernel

public theorem not_seven_dvd_card_kernel
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* He) (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    ¬7 ∣ Nat.card f.ker := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hp : IsPGroup 7 seven := IsPGroup.of_card (n := 3) card_seven
  have hi := not_dvd_index_of_card seven (p := 7) (n := 3) card_seven (by decide)
  exact SporadicTrivialMultipliers.OddPrimary.not_dvd_card_kernel_of_scaled_pair
    f hf hk 2 4 (by decide) (by decide) (by decide) (by decide) (hp.toSylow hi)
    sevenEigenFirst sevenEigenSecond sevenActor seven_pair_generates seven_first_pow seven_second_pow
    seven_commutator_ne seven_first_comm seven_second_comm seven_actor_first seven_actor_second seven_actor_comm

end Held.OddPrimary
