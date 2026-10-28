module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupAction.NoncentralTwoChiefLength.Native
import Mathlib.Tactic
/-!
# Cubic conjugation on the syntheme two-core

The two-core of the stabilizer of `{{0,1},{2,3},{4,5}}` is the cube D
of the three within-pair swaps. Its even subgroup D0 has order four.
The pair rotation fixes two elements of D and only the identity of D0;
both actual centralizer indices are therefore four. Its action on D/D0
is trivial, as recorded by the commutator containment.

The core bound uses a Sylow Borel and its conjugate under the pair rotation.
Their intersection inside the parabolic is D. The finite certificates
check conjugation and this intersection using the complete permutation
list, with all computation checked by the Lean kernel.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma 13.8.33, printed p.968 (the canonical model calculation).
-/

@[expose] public section

open Subgroup
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped commutatorElement

private def cubeWords : List S :=
  [1, swap01, swap23, swap45, swap01 * swap23, swap01 * swap45,
    swap23 * swap45, swap01 * swap23 * swap45]

private theorem cube_mul_cert : cubeWords.all (fun g =>
    cubeWords.all (fun h => decide (g * h ∈ cubeWords))) = true := by decide
private theorem cube_inv_cert : cubeWords.all (fun g => decide (g⁻¹ ∈ cubeWords)) = true := by decide

private def cubeGroup : Subgroup S where
  carrier := {g | g ∈ cubeWords}
  one_mem' := by decide
  mul_mem' := by
    have hc : ∀ g ∈ cubeWords, ∀ h ∈ cubeWords, g * h ∈ cubeWords := by
      simpa only [List.all_eq_true, decide_eq_true_eq] using cube_mul_cert
    exact fun _ _ hg hh => hc _ hg _ hh
  inv_mem' := by
    have hc : ∀ g ∈ cubeWords, g⁻¹ ∈ cubeWords := by
      simpa only [List.all_eq_true, decide_eq_true_eq] using cube_inv_cert
    exact fun _ hg => hc _ hg

private local instance (g : S) : Decidable (g ∈ cubeGroup) := inferInstanceAs (Decidable (g ∈ cubeWords))

private theorem D_eq_cubeGroup : D = cubeGroup := by
  apply le_antisymm
  · rw [D, closure_le]
    intro g hg
    rcases hg with rfl | rfl | rfl <;> change _ ∈ cubeWords <;> decide
  · intro g hg
    change g ∈ cubeWords at hg
    simp only [cubeWords, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact swap01_mem_D
    · exact swap23_mem_D
    · exact swap45_mem_D
    · exact mul_mem swap01_mem_D swap23_mem_D
    · exact mul_mem swap01_mem_D swap45_mem_D
    · exact mul_mem swap23_mem_D swap45_mem_D
    · exact mul_mem (mul_mem swap01_mem_D swap23_mem_D) swap45_mem_D

private local instance : Fintype cubeGroup :=
  Fintype.ofFinset cubeWords.toFinset (by intro g; simp; rfl)

theorem D_card : Nat.card D = 8 := by
  rw [D_eq_cubeGroup, Nat.card_eq_fintype_card]
  decide

theorem D_isPGroup : IsPGroup 2 D := IsPGroup.of_card (D_card.trans (by decide : 8 = 2 ^ 3))

def pairRotation : S :=
  (Equiv.swap 0 2 * Equiv.swap 2 4) * (Equiv.swap 1 3 * Equiv.swap 3 5)

private def synthemeWords : List S :=
  (permsOfList [0, 1, 2, 3, 4, 5]).filter (fun g => decide (g ∈ H2))

private theorem mem_synthemeWords {g : S} (hg : g ∈ H2) : g ∈ synthemeWords := by
  apply List.mem_filter.mpr
  refine ⟨mem_permsOfList_of_mem ?_, by simpa using hg⟩
  intro i _
  fin_cases i <;> simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem normal_cert : synthemeWords.all (fun g =>
    cubeWords.all (fun d => decide (g * d * g⁻¹ ∈ cubeWords))) = true := by decide +kernel

theorem H2_normalizes_D : H2 ≤ normalizer (D : Set S) := by
  have hc : ∀ g ∈ synthemeWords, ∀ d ∈ cubeWords, g * d * g⁻¹ ∈ cubeWords := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using normal_cert
  apply (normal_subgroupOf_iff_le_normalizer D_le_H2).mp
  constructor
  intro d hd g
  change (g : S) * (d : S) * (g : S)⁻¹ ∈ D
  rw [D_eq_cubeGroup] at hd ⊢
  exact hc g (mem_synthemeWords g.property) d hd

private theorem H2_normalizes_core : H2 ≤ normalizer (H2.pCoreIn 2 : Set S) :=
  H2.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H2 (pCore 2 H2))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem core_bound_cert : synthemeWords.all (fun g =>
    decide (g ∈ borel → pairRotation * g * pairRotation⁻¹ ∈ borel → g ∈ cubeGroup)) = true := by
  decide +kernel

theorem H2_core_eq_D : H2.pCoreIn 2 = D := by
  apply le_antisymm
  · let B := borel.subgroupOf H2
    have hpB : IsPGroup 2 B := borelSylow.isPGroup'.comap_subtype
    have hi : B.index = 3 := borel_relIndex_syntheme
    let T : Sylow 2 H2 := hpB.toSylow (by rw [hi]; decide)
    have hb : H2.pCoreIn 2 ≤ borel := by
      have ht := pCoreIn_le_sylow H2 T
      change H2.pCoreIn 2 ≤ B.map H2.subtype at ht
      exact ht.trans_eq (map_subgroupOf_eq_of_le (show borel ≤ H2 from borel_le_synthemeStabilizer))
    intro g hg
    have hconj : pairRotation * g * pairRotation⁻¹ ∈ H2.pCoreIn 2 :=
      (mem_normalizer_iff.mp (H2_normalizes_core (by decide : pairRotation ∈ H2)) g).mp hg
    have hc : ∀ g ∈ synthemeWords,
        g ∈ borel → pairRotation * g * pairRotation⁻¹ ∈ borel → g ∈ cubeGroup := by
      simpa only [List.all_eq_true, decide_eq_true_eq] using core_bound_cert
    rw [D_eq_cubeGroup]
    exact hc g (mem_synthemeWords (pCoreIn_le 2 H2 hg)) (hb hg) (hb hconj)
  · exact le_pCoreIn_of_normalizes D_isPGroup D_le_H2 H2_normalizes_D

theorem pairRotation_mem_H2 : pairRotation ∈ H2 := by decide

theorem H2_normalizes_D0 : H2 ≤ normalizer (D0 : Set S) :=
  (le_inf H2_normalizes_D le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf

private def evenCubeWords : List S :=
  [1, swap01 * swap23, swap01 * swap45, swap23 * swap45]

private theorem D0_words (g : S) : g ∈ D0 ↔ g ∈ evenCubeWords := by
  change g ∈ D ∧ g ∈ alternatingGroup (Fin 6) ↔ _
  rw [D_eq_cubeGroup]
  change g ∈ cubeWords ∧ g ∈ alternatingGroup (Fin 6) ↔ _
  constructor
  · rintro ⟨hg, he⟩
    simp only [cubeWords, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | decide | (exfalso; revert he; decide)
  · intro hg
    simp only [evenCubeWords, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> decide

private local instance : Fintype D0 :=
  Fintype.ofFinset evenCubeWords.toFinset (by intro g; simp only [List.mem_toFinset]; exact (D0_words g).symm)

theorem D0_card : Nat.card D0 = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem D0_cases {g : S} (hg : g ∈ D0) :
    g = 1 ∨ g = swap01 * swap23 ∨ g = swap01 * swap45 ∨ g = swap23 * swap45 := by
  simpa only [evenCubeWords, List.mem_cons, List.not_mem_nil, or_false] using (D0_words g).mp hg

private theorem rotation_centralizer :
    centralizer (zpowers pairRotation : Set S) = centralizer {pairRotation} := by
  rw [zpowers_eq_closure, centralizer_closure]

private def fixedCubeWords : List S := [1, swap01 * swap23 * swap45]

private theorem fixed_cube_words (g : S) :
    g ∈ centralizer {pairRotation} ⊓ D ↔ g ∈ fixedCubeWords := by
  change (∀ x ∈ ({pairRotation} : Set S), x * g = g * x) ∧ g ∈ D ↔ _
  rw [D_eq_cubeGroup]
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨hc, hg⟩
    change g ∈ cubeWords at hg
    simp only [cubeWords, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | decide | (exfalso; revert hc; decide)
  · intro hg
    simp only [fixedCubeWords, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> constructor <;> decide

private theorem fixed_D_card : Nat.card ↥(centralizer {pairRotation} ⊓ D) = 2 := by
  let : Fintype ↥(centralizer {pairRotation} ⊓ D) :=
    Fintype.ofFinset fixedCubeWords.toFinset
      (by intro g; simp only [List.mem_toFinset]; exact (fixed_cube_words g).symm)
  rw [Nat.card_eq_fintype_card]
  decide

theorem rotation_fixedIndex_D : (centralizer (zpowers pairRotation : Set S)).relIndex D = 4 := by
  rw [rotation_centralizer]
  have h := relIndex_mul_relIndex (⊥ : Subgroup S) (centralizer {pairRotation} ⊓ D) D
    bot_le inf_le_right
  rw [relIndex_bot_left, relIndex_bot_left, fixed_D_card, D_card, inf_relIndex_right] at h
  omega

theorem rotation_fixedIndex_D0 : (centralizer (zpowers pairRotation : Set S)).relIndex D0 = 4 := by
  rw [rotation_centralizer]
  have hc : centralizer {pairRotation} ⊓ D0 = ⊥ := by
    apply le_bot_iff.mp
    intro g hg
    have he := (mem_centralizer_iff.mp hg.1) pairRotation (by simp)
    rcases D0_cases hg.2 with rfl | rfl | rfl | rfl
    · exact one_mem _
    all_goals (exfalso; revert he; decide)
  rw [← inf_relIndex_right, hc, relIndex_bot_left, D0_card]

open scoped commutatorElement in
/-- The cubic action is trivial on the section between the even cube and the cube. -/
theorem rotation_commutator_le_D0 : ⁅zpowers pairRotation, D⁆ ≤ D0 := by
  apply le_inf
  · exact le_normalizer_iff_commutator_le_right.mp
      (zpowers_le.mpr (H2_normalizes_D pairRotation_mem_H2))
  · rw [commutator_le]
    intro g _ d _
    change Equiv.Perm.sign ⁅g, d⁆ = 1
    simp [commutatorElement_def, mul_assoc, mul_left_comm, mul_comm]
end Theory.SpecificGroups.SymmetricSix.BinaryFlags
