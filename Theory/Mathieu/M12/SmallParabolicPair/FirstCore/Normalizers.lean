module

public import Theory.Mathieu.M12.SmallParabolicPair.FirstCore.Order

/-!
# Invariance of the marked quaternion factors

The kernel and two explicit lifts of generators of S₃ generate the first
parabolic. Each normalizes both marked quaternion factors, as verified on the
quaternion coordinates. Thus the entire first parabolic preserves both factors.
Source: the M₁₂ local structure in Aschbacher–Smith, Lemma 14.2.21.
-/

@[expose] public section
open Sporadic.Mathieu
namespace Sporadic.Mathieu.M12SmallPair.FirstCore
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem core_normalizes_left : core ≤ Subgroup.normalizer (leftFactor : Set M12) := by
  apply sup_le leftFactor.le_normalizer
  apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  intro r hr l hl
  exact factors_commute l hl r hr

theorem core_normalizes_right : core ≤ Subgroup.normalizer (rightFactor : Set M12) := by
  apply sup_le ?_ rightFactor.le_normalizer
  apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  intro l hl r hr
  exact (factors_commute l hl r hr).symm

theorem secondCycle_normalizes_left : secondCycle ∈ Subgroup.normalizer (leftFactor : Set M12) := by
  apply Subgroup.mem_normalizer_fintype
  rintro _ ⟨q,rfl⟩
  have h : ∀ q : QuaternionGroup 2, ∃ r : QuaternionGroup 2,
      leftEmbedding r = secondCycle * leftEmbedding q * secondCycle⁻¹ := by decide +kernel
  exact h q

theorem secondCycle_normalizes_right : secondCycle ∈ Subgroup.normalizer (rightFactor : Set M12) := by
  apply Subgroup.mem_normalizer_fintype
  rintro _ ⟨q,rfl⟩
  have h : ∀ q : QuaternionGroup 2, ∃ r : QuaternionGroup 2,
      rightEmbedding r = secondCycle * rightEmbedding q * secondCycle⁻¹ := by decide +kernel
  exact h q

theorem secondSwap_normalizes_left : secondSwap ∈ Subgroup.normalizer (leftFactor : Set M12) := by
  apply Subgroup.mem_normalizer_fintype
  rintro _ ⟨q,rfl⟩
  have h : ∀ q : QuaternionGroup 2, ∃ r : QuaternionGroup 2,
      leftEmbedding r = secondSwap * leftEmbedding q * secondSwap⁻¹ := by decide +kernel
  exact h q

theorem secondSwap_normalizes_right : secondSwap ∈ Subgroup.normalizer (rightFactor : Set M12) := by
  apply Subgroup.mem_normalizer_fintype
  rintro _ ⟨q,rfl⟩
  have h : ∀ q : QuaternionGroup 2, ∃ r : QuaternionGroup 2,
      rightEmbedding r = secondSwap * rightEmbedding q * secondSwap⁻¹ := by decide +kernel
  exact h q


theorem cycle_image : matchingQuotient ⟨secondCycle, secondCycle_mem⟩ =
    List.formPerm [0,2,1] := by
  change matchingAction (fixedPointAction ⟨secondCycle, secondCycle_mem⟩) = _
  have hfour : fixedPointAction ⟨secondCycle, secondCycle_mem⟩ =
      List.formPerm [1,3,2] := by
    apply second_four_action_eq
    decide +kernel
  rw [hfour]
  apply matching_action_eq
  decide +kernel

theorem swap_image : matchingQuotient ⟨secondSwap, secondSwap_mem⟩ =
    Equiv.swap 1 2 := by
  change matchingAction (fixedPointAction ⟨secondSwap, secondSwap_mem⟩) = _
  have hfour : fixedPointAction ⟨secondSwap, secondSwap_mem⟩ =
      List.formPerm [0,2,1,3] := by
    apply second_four_action_eq
    decide +kernel
  rw [hfour]
  apply matching_action_eq
  decide +kernel

theorem firstParabolic_le_of_core_cycle_swap (N : Subgroup M12)
    (hcore : core ≤ N) (hcycle : secondCycle ∈ N) (hswap : secondSwap ∈ N) :
    firstParabolic ≤ N := by
  let S := N.subgroupOf firstParabolic
  let f := matchingQuotient.comp S.subtype
  have hsurj : Function.Surjective f := by
    apply surjective_of_two_images f
      ⟨⟨secondCycle,secondCycle_mem⟩,hcycle⟩ ⟨⟨secondSwap,secondSwap_mem⟩,hswap⟩
      (List.formPerm [0,2,1]) (Equiv.swap 1 2)
    · exact cycle_image
    · exact swap_image
    · decide +kernel
  have hker : matchingQuotient.ker ≤ S := by
    rw [← core_eq_matching_ker]
    intro g hg
    exact hcore hg
  intro g hg
  let gH : firstParabolic := ⟨g,hg⟩
  obtain ⟨x,hx⟩ := hsurj (matchingQuotient gH)
  have hk : gH * (x : firstParabolic)⁻¹ ∈ matchingQuotient.ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_mul, map_inv]
    change matchingQuotient (x : firstParabolic) = matchingQuotient gH at hx
    rw [hx, mul_inv_cancel]
  have hmem := S.mul_mem (hker hk) x.property
  have : gH ∈ S := by simpa only [inv_mul_cancel_right] using hmem
  exact this

end Sporadic.Mathieu.M12SmallPair.FirstCore
namespace Sporadic.Mathieu.M12SmallPair
open FirstCore

theorem firstParabolic_normalizes_left : firstParabolic ≤ Subgroup.normalizer (leftFactor : Set M12) :=
  firstParabolic_le_of_core_cycle_swap _ core_normalizes_left
    secondCycle_normalizes_left secondSwap_normalizes_left

theorem firstParabolic_normalizes_right : firstParabolic ≤ Subgroup.normalizer (rightFactor : Set M12) :=
  firstParabolic_le_of_core_cycle_swap _ core_normalizes_right
    secondCycle_normalizes_right secondSwap_normalizes_right

end Sporadic.Mathieu.M12SmallPair
