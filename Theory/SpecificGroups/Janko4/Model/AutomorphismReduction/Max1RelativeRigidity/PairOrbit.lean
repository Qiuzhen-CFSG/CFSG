module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1RelativeRigidity.Core
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1RelativeRigidity.OrbitData
public import Mathlib.GroupTheory.GroupAction.Quotient
/-!
# Exact orbit and centralizer count for the actual max1 kernel pair

The checked membership predicate marks exactly 1771 binary masks and is
preserved by both right-conjugation tables. Finiteness and generation extend
invariance to every element of max1. Conversely, descent in the existing
2048-mask parent tree reaches mask three for every marked mask. The coordinate
bijection therefore identifies this finite set with the actual local orbit.
Orbit-stabilizer and the certified max1 order yield centralizer order 283115520.

The conjugation transfer follows the checked orbit-tree argument in
`Max1Fusion.KernelOrbits`; finite inverse invariance follows the argument in
`MathieuSeedCentralizer.LocalLowerBound`. The subgroup and tables come from
literal ATLAS `J4G1-max1W1`, documented in `Cardinality.Subgroup`.
-/

set_option maxRecDepth 10000
public section
namespace Janko4.Max1RelativeRigidity
open Cardinality Cardinality.KernelCount Cardinality.QuotientCount.Image
open Simplicity.Max1Fusion Simplicity.Max1Fusion.KernelOrbits OrbitData
attribute [local irreducible] basis modelGroup matrixA matrixB localKernel
  max1Subgroup localX localY localKernelSeed

private noncomputable def pairValue (m : PairMask) : M := maskEquiv m.val
private def pairSet : Set M := Set.range pairValue

private theorem pairValue_injective : Function.Injective pairValue := by
  intro m n h
  apply Subtype.ext
  apply maskEquiv.injective
  exact Subtype.ext h

private theorem pairSet_card : Nat.card pairSet = 1771 :=
  (Nat.card_congr (Equiv.ofInjective pairValue pairValue_injective).symm).trans pairMask_card

private theorem pair_mem_pairSet : v ∈ pairSet :=
  ⟨⟨3, three_mem⟩, maskValue_three matrixA_mul_self matrixB_pow_four⟩

private theorem pairSet_conj_x : ∀ z ∈ pairSet, x⁻¹ * z * x ∈ pairSet := by
  rintro z ⟨m, rfl⟩
  change x⁻¹ * (maskValue matrixA_mul_self matrixB_pow_four m.val.val : M) * x ∈ _
  rw [right_conj_mask_x]
  refine ⟨⟨⟨maskImage xMasks m.val.val, (certificate m.val).1⟩, ?_⟩, rfl⟩
  exact (certificate m.val).2.2.1.trans m.property

private theorem pairSet_conj_y : ∀ z ∈ pairSet, y⁻¹ * z * y ∈ pairSet := by
  rintro z ⟨m, rfl⟩
  change y⁻¹ * (maskValue matrixA_mul_self matrixB_pow_four m.val.val : M) * y ∈ _
  rw [right_conj_mask_y]
  refine ⟨⟨⟨maskImage yMasks m.val.val, (certificate m.val).2.1⟩, ?_⟩, rfl⟩
  exact (certificate m.val).2.2.2.1.trans m.property

private theorem conjugate_mem_of_inv (S : Set M) (g : M)
    (h : ∀ z ∈ S, g⁻¹ * z * g ∈ S) : ∀ z ∈ S, g * z * g⁻¹ ∈ S := by
  let f : S → S := fun z => ⟨g⁻¹ * z * g, h z z.property⟩
  have hf : Function.Injective f := by
    intro z w he
    apply Subtype.ext
    exact mul_left_cancel (mul_right_cancel (congrArg Subtype.val he))
  intro z hz
  obtain ⟨w, hw⟩ := Finite.surjective_of_injective hf ⟨z, hz⟩
  have he := congrArg (fun v : S => g * (v : M) * g⁻¹) hw
  have he' : (w : M) = g * z * g⁻¹ := by simpa [f, mul_assoc] using he
  exact he' ▸ w.property

private theorem pairSet_conj (g : M) : ∀ z ∈ pairSet, g * z * g⁻¹ ∈ pairSet := by
  have hg : g ∈ Subgroup.closure {x, y} := by
    rw [localXY_generate]; trivial
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · exact conjugate_mem_of_inv _ _ pairSet_conj_x
    · obtain rfl := Set.mem_singleton_iff.mp hg
      exact conjugate_mem_of_inv _ _ pairSet_conj_y
  | one => simp
  | mul g k _ _ ihg ihk =>
    intro z hz
    simpa only [mul_inv_rev, mul_assoc] using ihg _ (ihk z hz)
  | inv g _ ih =>
    simpa only [inv_inv] using conjugate_mem_of_inv pairSet g⁻¹
      (by simpa only [inv_inv] using ih)

/-- Membership is also sufficient: the existing checked parent tree reaches mask three. -/
theorem mask_isConj_pair (m : Fin 2048) (hm : inPairOrbit m.val = true) :
    IsConj (maskEquiv m : M) v := by
  suffices ∀ d (m : Fin 2048), depth m = d → inPairOrbit m.val = true →
      IsConj (maskEquiv m : M) v from this (depth m) m rfl hm
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro m hd hm
    rcases tree_certificate m with h0 | h1 | h3 | ⟨hlt, he⟩
    · subst m
      exact Bool.noConfusion (zero_not_mem.symm.trans hm)
    · subst m
      exact Bool.noConfusion (one_not_mem.symm.trans hm)
    · subst m
      change IsConj (maskValue matrixA_mul_self matrixB_pow_four 3 : M) v
      rw [maskValue_three]
    · have hc : IsConj (maskEquiv (parent m) : M) (maskEquiv m : M) := by
        rcases he with hx | hy
        · exact isConj_iff.mpr ⟨x⁻¹, by
            simpa only [maskEquiv_apply, inv_inv, hx] using
              right_conj_mask_x matrixA_mul_self matrixB_pow_four (parent m).val⟩
        · exact isConj_iff.mpr ⟨y⁻¹, by
            simpa only [maskEquiv_apply, inv_inv, hy] using
              right_conj_mask_y matrixA_mul_self matrixB_pow_four (parent m).val⟩
      exact hc.symm.trans (ih (depth (parent m)) (hlt.trans_eq hd) (parent m) rfl
        ((certificate m).2.2.2.2.trans hm))

private theorem pair_orbit_eq : MulAction.orbit (ConjAct M) v = pairSet := by
  apply Set.Subset.antisymm
  · rintro z ⟨g, rfl⟩
    exact pairSet_conj g.ofConjAct v pair_mem_pairSet
  · rintro z ⟨m, rfl⟩
    exact ConjAct.mem_orbit_conjAct.mpr (mask_isConj_pair m.val m.property)

/-- The conjugacy orbit of the actual kernel pair inside actual max1 has size 1771. -/
theorem pair_orbit_card : Nat.card (MulAction.orbit (ConjAct M) v) = 1771 := by
  rw [pair_orbit_eq]
  exact pairSet_card

/-- The centralizer index is computed in max1, rather than in the ambient J4 group. -/
theorem pair_centralizer_index : (Subgroup.centralizer ({v} : Set M)).index = 1771 := by
  have h := pair_orbit_card
  rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (ConjAct M) v),
    ConjAct.stabilizer_eq_centralizer] at h
  exact h

/-- The actual overlap with the ambient centralizer has order 283115520. -/
theorem pair_centralizer_card : Nat.card (Subgroup.centralizer ({v} : Set M)) = 283115520 := by
  have h := (Subgroup.centralizer ({v} : Set M)).card_mul_index
  rw [pair_centralizer_index] at h
  change Nat.card (Subgroup.centralizer ({v} : Set M)) * 1771 =
    Nat.card (max1Subgroup matrixA_mul_self matrixB_pow_four) at h
  rw [max1Subgroup_card matrixA_mul_self matrixB_pow_four] at h
  omega
end Janko4.Max1RelativeRigidity
