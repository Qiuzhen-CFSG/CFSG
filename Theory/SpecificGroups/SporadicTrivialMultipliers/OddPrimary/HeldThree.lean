module
public import Theory.SpecificGroups.SporadicTrivialMultipliers.OddPrimary.HeldBounds
public import Theory.SpecificGroups.Held.OddCubeCandidates.Cardinality
public import Theory.SpecificGroups.Held.Model.FourPointBase
public import Theory.GroupTheory.PerfectCentralCoverSylowNine.OddInversion
public import Theory.GroupTheory.PGroup.ExtraspecialPrimeCube

/-!
# Three-primary kernels over Held

The literal order-27 subgroup is Sylow by the proved ambient odd-order
bound. A word in the existing max3 generators inverts its two generators.
Its action is checked on the actual four-point base; central-commutator
identities use the already-certified compact permutation tables.
Simultaneous-inversion transfer then excludes three from every finite
perfect central kernel. Source: Aschbacher–Smith I.1.3, printed p.407;
ATLAS HeG1-max3W1 and HeG1-p2058B0.
-/

open Subgroup
open scoped commutatorElement
namespace Held.OddPrimary
open OddCubeCandidates CardinalityCertificates

private def threeActor : He :=
  let x := a
  let y := LocalPairs.PairCoverage.localWord false
  y ^ (-3 : ℤ) * x * y * x * y⁻¹ * x * y ^ (-3 : ℤ) * x * y * x * y⁻¹ * x

private theorem three_first_pow : threeFirst ^ 3 = 1 := by
  apply eq_of_four_point_images
  decide +kernel
private theorem three_second_pow : threeSecond ^ 3 = 1 := by
  apply eq_of_four_point_images
  decide +kernel
private theorem three_first_comm : Commute threeFirst ⁅threeFirst, threeSecond⁆ := by
  change threeFirst * ⁅threeFirst, threeSecond⁆ = ⁅threeFirst, threeSecond⁆ * threeFirst
  apply eq_of_four_point_images
  simp only [commutatorElement_def, map_mul, map_inv]
  rw [← threeX_eq, ← threeY_eq]
  decide +kernel
private theorem three_second_comm : Commute threeSecond ⁅threeFirst, threeSecond⁆ := by
  change threeSecond * ⁅threeFirst, threeSecond⁆ = ⁅threeFirst, threeSecond⁆ * threeSecond
  apply eq_of_four_point_images
  simp only [commutatorElement_def, map_mul, map_inv]
  rw [← threeX_eq, ← threeY_eq]
  decide +kernel
private theorem three_actor_first : threeActor * threeFirst * threeActor⁻¹ = threeFirst⁻¹ := by
  apply eq_of_four_point_images
  decide +kernel
private theorem three_actor_second : threeActor * threeSecond * threeActor⁻¹ = threeSecond⁻¹ := by
  apply eq_of_four_point_images
  decide +kernel
private theorem three_actor_comm : Commute threeActor ⁅threeFirst, threeSecond⁆ := by
  apply mul_inv_eq_iff_eq_mul.mp
  rw [conjugate_commutatorElement, three_actor_first, three_actor_second,
    commutatorElement_inv_right threeFirst⁻¹ threeSecond,
    commutatorElement_inv_right threeSecond threeFirst,
    three_first_comm.inv_left.eq, inv_mul_cancel_right,
    three_second_comm.inv_left.eq, inv_mul_cancel_right]

public theorem exists_three_configuration :
    ∃ (Q : Sylow 3 He) (x y r : He),
      closure ({x, y} : Set He) = (Q : Subgroup He) ∧
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧
      Commute x ⁅x, y⁆ ∧ Commute y ⁅x, y⁆ ∧
      r * x * r⁻¹ = x⁻¹ ∧ r * y * r⁻¹ = y⁻¹ ∧ Commute r ⁅x, y⁆ := by
  have hp : IsPGroup 3 three := IsPGroup.of_card (n := 3) card_three
  have hi := not_dvd_index_of_card three (p := 3) (n := 3) card_three (by decide)
  refine ⟨hp.toSylow hi, threeFirst, threeSecond, threeActor, rfl,
    three_first_pow, three_second_pow, ?_, three_first_comm, three_second_comm,
    three_actor_first, three_actor_second, three_actor_comm⟩
  exact fun h => three_mul_ne_mul (commutatorElement_eq_one_iff_mul_comm.mp h)

public theorem not_three_dvd_card_kernel
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* He) (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    ¬3 ∣ Nat.card f.ker := by
  obtain ⟨Q, x, y, r, hQ, hx, hy, hz, hxz, hyz, hrx, hry, hrz⟩ := exists_three_configuration
  exact PerfectCentralCovering.not_dvd_card_kernel_of_simultaneous_inversion_of_ne_two
    f hf hk (by decide : 3 ≠ 2) Q x y r hQ hx hy hz hxz hyz hrx hry hrz

end Held.OddPrimary
