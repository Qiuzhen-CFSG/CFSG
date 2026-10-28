module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.KernelOrbits.Coordinates
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# A lower bound for the centralizer of the max1 kernel seed

The 24-star pair labels form a set of at most 276 actual elements of the
binary kernel. The certified tables show that conjugation by either local
generator preserves this set. Finiteness supplies inverse invariance, and
local generation then puts the entire local conjugacy orbit of `(xy)^14`
in this set. Orbit-stabilizer and the certified max1 order give a centralizer
of order at least 1816657920 inside the literal max1 subgroup.

This is a lower bound inside max1, not an upper bound in the ambient model.
The companion module uses it for an order-comparison reduction of ambient
containment. No vector-stabilizer identification or ambient order is used.

Source: the ATLAS `J4G1-max1W1` words and the checked pair labels documented
in `Cardinality.Subgroup` and `QuotientCount.Image.StarData`; the expected
2B centralizer is recorded in GLS3, Table 5.3i, printed p.270.
-/

public section

open Subgroup
namespace Janko4.LocalStructure.MathieuSeedCentralizer
open Cardinality Cardinality.QuotientCount.Image Simplicity.Max1Fusion.KernelOrbits
variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localX localY localKernelSeed

private abbrev PairIndex := {p : Fin 24 × Fin 24 // p.1 < p.2}
private theorem pairIndex_card : Nat.card PairIndex = 276 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private def pairValue (p : PairIndex) : max1Subgroup hA hB :=
  maskValue hA hB (pairLabel p.val.1 p.val.2)

private def pairSet : Set (max1Subgroup hA hB) := Set.range (pairValue hA hB)

private theorem pair_mem (i j : Fin 24) (hij : i ≠ j) :
    (maskValue hA hB (pairLabel i j) : max1Subgroup hA hB) ∈ pairSet hA hB := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨⟨(i,j), h⟩, rfl⟩
  · exact ⟨⟨(j,i), h⟩, by simp only [pairValue, pairLabel_symm]⟩

private theorem seed_mem_pairSet : localKernelSeed hA hB ∈ pairSet hA hB := by
  have h := pair_mem hA hB 0 1 (by decide)
  simpa only [show pairLabel 0 1 = 1 from rfl, maskValue_one] using h

private theorem pairSet_card_le : Nat.card (pairSet hA hB) ≤ 276 := by
  rw [← pairIndex_card]
  exact Nat.card_le_card_of_surjective
    (fun p : PairIndex => (⟨pairValue hA hB p, p, rfl⟩ : pairSet hA hB))
    (by rintro ⟨z, p, rfl⟩; exact ⟨p, rfl⟩)

private theorem pairSet_conj_x : ∀ z ∈ pairSet hA hB,
    (localX hA hB)⁻¹ * z * localX hA hB ∈ pairSet hA hB := by
  rintro z ⟨p, rfl⟩
  change (localX hA hB)⁻¹ * (maskValue hA hB _) * localX hA hB ∈ _
  rw [right_conj_mask_x, ← pairLabel_rightX]
  exact pair_mem hA hB _ _ (rightX.injective.ne p.property.ne)

private theorem pairSet_conj_y : ∀ z ∈ pairSet hA hB,
    (localY hA hB)⁻¹ * z * localY hA hB ∈ pairSet hA hB := by
  rintro z ⟨p, rfl⟩
  change (localY hA hB)⁻¹ * (maskValue hA hB _) * localY hA hB ∈ _
  rw [right_conj_mask_y, ← pairLabel_rightY]
  exact pair_mem hA hB _ _ (rightY.injective.ne p.property.ne)

private theorem conjugate_mem_of_inv {G : Type*} [Group G] [Finite G]
    (S : Set G) (g : G) (h : ∀ z ∈ S, g⁻¹ * z * g ∈ S) :
    ∀ z ∈ S, g * z * g⁻¹ ∈ S := by
  let f : S → S := fun z => ⟨g⁻¹ * z * g, h z z.property⟩
  have hf : Function.Injective f := by
    intro z w he
    apply Subtype.ext
    exact mul_left_cancel (mul_right_cancel (congrArg Subtype.val he))
  intro z hz
  obtain ⟨w, hw⟩ := Finite.surjective_of_injective hf ⟨z, hz⟩
  have he := congrArg (fun v : S => g * (v : G) * g⁻¹) hw
  have he' : (w : G) = g * z * g⁻¹ := by simpa [f, mul_assoc] using he
  exact he' ▸ w.property

private theorem pairSet_conj (g : max1Subgroup hA hB) :
    ∀ z ∈ pairSet hA hB, g * z * g⁻¹ ∈ pairSet hA hB := by
  have hg : g ∈ Subgroup.closure {localX hA hB, localY hA hB} := by
    rw [localXY_generate]; trivial
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · exact conjugate_mem_of_inv _ _ (pairSet_conj_x hA hB)
    · obtain rfl := Set.mem_singleton_iff.mp hg
      exact conjugate_mem_of_inv _ _ (pairSet_conj_y hA hB)
  | one => simp
  | mul g k _ _ ihg ihk =>
    intro z hz
    simpa only [mul_inv_rev, mul_assoc] using ihg _ (ihk z hz)
  | inv g _ ih =>
    simpa only [inv_inv] using conjugate_mem_of_inv (pairSet hA hB) g⁻¹
      (by simpa only [inv_inv] using ih)

private theorem seed_orbit_card_le :
    Nat.card (MulAction.orbit (ConjAct (max1Subgroup hA hB)) (localKernelSeed hA hB)) ≤ 276 := by
  have hi : MulAction.orbit (ConjAct (max1Subgroup hA hB)) (localKernelSeed hA hB) ⊆
      pairSet hA hB := by
    rintro z ⟨g, rfl⟩
    exact pairSet_conj hA hB g.ofConjAct _ (seed_mem_pairSet hA hB)
  exact (Nat.card_le_card_of_injective (Set.inclusion hi)
    (Set.inclusion_injective hi)).trans (pairSet_card_le hA hB)

/-- The actual local seed has at least this many centralizing elements in max1. -/
theorem localSeedCentralizer_card_ge :
    1816657920 ≤ Nat.card (Subgroup.centralizer
      ({localKernelSeed hA hB} : Set (max1Subgroup hA hB))) := by
  have hc := (Subgroup.centralizer ({localKernelSeed hA hB} : Set (max1Subgroup hA hB))).card_mul_index
  have he := MulAction.orbitEquivQuotientStabilizer
    (ConjAct (max1Subgroup hA hB)) (localKernelSeed hA hB)
  have hindex : (Subgroup.centralizer ({localKernelSeed hA hB} : Set (max1Subgroup hA hB))).index ≤ 276 := by
    have h := seed_orbit_card_le hA hB
    rw [Nat.card_congr he, ConjAct.stabilizer_eq_centralizer] at h
    exact h
  rw [max1Subgroup_card] at hc
  nlinarith
end Janko4.LocalStructure.MathieuSeedCentralizer
