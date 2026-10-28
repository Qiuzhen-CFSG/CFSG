module
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.StageZero.Representatives

/-!
# The two supplied Schreier factors on the stage-zero tree

The source words 3, 4, 6 and 7 coincide with four actual defining-tree words.
Checking their individual parent edges keeps recursive representative reduction
shallow. The definitions of words 5 and 8 then give two full-degree transitions
with explicit factors in stage 1. These are seed transitions, not the whole table.

Source: ATLAS F24G1-p306936B0, GLS3 Table 5.3v, and the exact nodes in
`Fi23InFi24Prime/source/faithfulness/nodes.json`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageZero
open Subgroup.CosetWordCertificate

private theorem right_edge (j p : Nat) (a : Fin 2) (hj : j ≠ 0)
    (hp : parent j = p) (ha : letter j = a) :
    definitions.repr (generators 0) j =
      definitions.repr (generators 0) p * generators 0 a := by
  have h := definitions.repr_edge (generators 0) j hj
  change definitions.repr (generators 0) (parent j) *
    eval (generators 0) [(letter j, true)] = definitions.repr (generators 0) j at h
  simpa only [eval_letter, ite_true, hp, ha] using h.symm

private theorem word3_right : Word.word3 aPerm bPerm =
    definitions.repr (generators 0) 25135 := by
  rw [right_edge 25135 22516 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 22516 19722 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 19722 16894 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 16894 14226 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 14226 11804 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 11804 9674 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 9674 7836 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 7836 6282 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 6282 5027 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 5027 4001 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 4001 3176 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 3176 2510 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 2510 1980 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 1980 1557 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 1557 1219 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 1219 950 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 950 737 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 737 570 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 570 439 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 439 338 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 338 260 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 260 198 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 198 150 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 150 112 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 112 83 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 83 61 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 61 44 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 44 32 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 32 22 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 22 15 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 15 10 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 10 6 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 6 3 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 3 1 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 1 0 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [Definitions.repr_zero]
  rfl

private theorem word4_right : Word.word4 aPerm bPerm =
    definitions.repr (generators 0) 24419 := by
  rw [right_edge 24419 21727 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 21727 18918 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 18918 16147 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 16147 13534 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 13534 11190 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 11190 9141 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 9141 7389 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 7389 5921 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 5921 4737 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 4737 3770 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 3770 2990 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 2990 2362 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 2362 1858 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 1858 1460 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 1460 1140 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 1140 889 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 889 690 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 690 534 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 534 412 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 412 317 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 317 243 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 243 185 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 185 139 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 139 104 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 104 77 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 77 56 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 56 41 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 41 29 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 29 20 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 20 14 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 14 9 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 9 5 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 5 2 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 2 0 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [Definitions.repr_zero]
  rfl

private theorem word6_right : Word.word6 aPerm bPerm =
    definitions.repr (generators 0) 15044 := by
  rw [right_edge 15044 12534 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 12534 10304 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 10304 8369 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 8369 6724 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 6724 5379 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 5379 4288 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 4288 3408 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 3408 2698 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 2698 2130 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 2130 1677 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 1677 1313 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 1313 1025 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 1025 796 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 796 616 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 616 475 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 475 366 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 366 281 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 281 216 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 216 163 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 163 123 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 123 91 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 91 67 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 67 49 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 49 35 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 35 25 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 25 17 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 17 11 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 11 7 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 7 3 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 3 1 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 1 0 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [Definitions.repr_zero]
  rfl

private theorem word7_right : Word.word7 aPerm bPerm =
    definitions.repr (generators 0) 16292 := by
  rw [right_edge 16292 13672 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 13672 11313 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 11313 9249 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 9249 7478 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 7478 5990 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 5990 4794 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 4794 3813 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 3813 3025 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 3025 2390 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 2390 1882 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 1882 1480 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 1480 1156 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 1156 902 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 902 699 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 699 541 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 541 417 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 417 321 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 321 246 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 246 188 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 188 141 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 141 106 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 106 78 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 78 57 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 57 42 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 42 30 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 30 21 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 21 14 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 14 9 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 9 5 0 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 5 2 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [right_edge 2 0 1 (by decide) (by decide +kernel) (by decide +kernel)]
  rw [Definitions.repr_zero]
  rfl

/-- The literal word5 is the factor for this nondefining transition. -/
theorem word5_transition :
    generators 0 1 * representative 24419 = representative 25135 * Word.word5 aPerm bPerm := by
  change bPerm * (definitions.repr (generators 0) 24419)⁻¹ =
    (definitions.repr (generators 0) 25135)⁻¹ * Word.word5 aPerm bPerm
  rw [Word.word5, word3_right, word4_right]
  simp only [mul_assoc, inv_mul_cancel_left]

/-- This seed supplies the exact positive-table step, including subgroup membership. -/
theorem seed5 : ∃ k : Fin 31671, ∃ h : stage 1,
    generators 0 1 * representative 24419 = representative k * h.val := by
  have hm : Word.word5 aPerm bPerm ∈ stage 1 := by
    apply Subgroup.subset_closure
    simp only [Word.generators, List.mem_cons]
    exact Or.inl rfl
  exact ⟨25135, ⟨Word.word5 aPerm bPerm, hm⟩, word5_transition⟩

/-- The literal word8 is the factor for this nondefining transition. -/
theorem word8_transition :
    generators 0 1 * representative 16292 = representative 15044 * Word.word8 aPerm bPerm := by
  change bPerm * (definitions.repr (generators 0) 16292)⁻¹ =
    (definitions.repr (generators 0) 15044)⁻¹ * Word.word8 aPerm bPerm
  rw [Word.word8, word6_right, word7_right]
  simp only [mul_assoc, inv_mul_cancel_left]

/-- This seed supplies the exact positive-table step, including subgroup membership. -/
theorem seed8 : ∃ k : Fin 31671, ∃ h : stage 1,
    generators 0 1 * representative 16292 = representative k * h.val := by
  have hm : Word.word8 aPerm bPerm ∈ stage 1 := by
    apply Subgroup.subset_closure
    simp only [Word.generators, List.mem_cons]
    exact Or.inr (Or.inl rfl)
  exact ⟨15044, ⟨Word.word8 aPerm bPerm, hm⟩, word8_transition⟩

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageZero
