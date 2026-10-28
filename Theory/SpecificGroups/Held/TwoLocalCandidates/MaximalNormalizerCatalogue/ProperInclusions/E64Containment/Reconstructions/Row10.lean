module
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.Reconstructions.FiniteEnumeration

/-!
# Checked enumeration and signatures for Held row 10

Binary products of the literal row generators enumerate this subgroup.
The multiplication table, distinctness, fixed-point counts and the two
span containments are checked in the actual degree-2058 representation.
The four-point base certifies group equalities, while fixed-point counts
check all 2058 vertices. No elementary-abelian hypothesis is assumed.

Sources: ATLAS HeG1-p2058B0, the unchanged catalogue words, GLS3 Table 5.3p.
-/

public section
namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.Reconstructions.Row10
open Subgroup ProperInclusions

@[expose] def indices (n : Fin 16) : List ℕ :=
  ([0, 1, 2, 3] : List ℕ).filter (fun i => n.val / 2 ^ i % 2 == 1)
@[expose] def element (n : Fin 16) : He := rowProduct 10 (indices n)
@[expose] def perm (n : Fin 16) : Equiv.Perm (Fin 2058) := permProduct 10 (indices n)
@[expose] def mulIdx (n m : Fin 16) : Fin 16 := Fin.ofNat 16 (n.val ^^^ m.val)
@[expose] def counts (n : Fin 16) : ℕ := ([2058, 154, 42, 154, 154, 154, 154, 154, 42, 154, 42, 154, 154, 154, 154, 154] : List ℕ)[n.val]?.getD 0

theorem perm_eq (n : Fin 16) : perm n = representation (element n) := permProduct_eq _ _
theorem element_mem (n : Fin 16) : element n ∈ ambient 10 := rowProduct_mem _ _
theorem element_zero : element 0 = 1 := rfl

set_option maxRecDepth 8192 in
private theorem mul_check : ∀ n m : Fin 16, ∀ v : Fin 4,
    (perm n * perm m) ⟨v.val, by omega⟩ = perm (mulIdx n m) ⟨v.val, by omega⟩ := by
  decide +kernel

theorem element_mul (n m : Fin 16) : element n * element m = element (mulIdx n m) := by
  apply eq_of_four_point_images
  simp only [map_mul, ← perm_eq]
  exact mul_check n m

set_option maxRecDepth 8192 in
private theorem injective_check : ∀ n m : Fin 16,
    (∀ v : Fin 4, perm n ⟨v.val, by omega⟩ = perm m ⟨v.val, by omega⟩) → n = m := by
  decide +kernel

theorem element_injective : Function.Injective element := by
  intro n m he
  apply injective_check
  intro v
  simp only [perm_eq, he]

@[expose] def generatorIndex (i : Fin 4) : Fin 16 :=
  Fin.ofNat 16 (([1, 2, 4, 8] : List ℕ)[i.val]?.getD 0)

set_option maxRecDepth 8192 in
private theorem generator_check : ∀ i : Fin 4, ∀ v : Fin 4,
    perm (generatorIndex i) ⟨v.val, by omega⟩ =
      permProduct 10 [i.val] ⟨v.val, by omega⟩ := by
  decide +kernel

theorem generator_eq (i : Fin 4) : element (generatorIndex i) = rowElement 10 i.val := by
  apply eq_of_four_point_images
  rw [← perm_eq, ← show rowProduct 10 [i.val] = rowElement 10 i.val by simp [rowProduct],
    ← permProduct_eq]
  exact generator_check i

theorem cover (x : He) : x ∈ ambient 10 ↔ ∃ n : Fin 16, element n = x := by
  apply enumeration 10 element element_mem ⟨0, element_zero⟩
  · intro n m
    exact ⟨mulIdx n m, element_mul n m⟩
  · intro n
    refine ⟨n, inv_eq_of_mul_eq_one_right ?_⟩
    rw [element_mul]
    have h : mulIdx n n = 0 := by simp [mulIdx]
    rw [h, element_zero]
  · intro w hw
    simp only [generatorWords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact ⟨generatorIndex 0, generator_eq 0⟩
    · exact ⟨generatorIndex 1, generator_eq 1⟩
    · exact ⟨generatorIndex 2, generator_eq 2⟩
    · exact ⟨generatorIndex 3, generator_eq 3⟩

set_option maxRecDepth 8192 in
private theorem count_0 : (List.finRange 2058).countP
    (fun v => decide (perm 0 v = v)) = 2058 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_1 : (List.finRange 2058).countP
    (fun v => decide (perm 1 v = v)) = 154 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_2 : (List.finRange 2058).countP
    (fun v => decide (perm 2 v = v)) = 42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_3 : (List.finRange 2058).countP
    (fun v => decide (perm 3 v = v)) = 154 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_4 : (List.finRange 2058).countP
    (fun v => decide (perm 4 v = v)) = 154 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_5 : (List.finRange 2058).countP
    (fun v => decide (perm 5 v = v)) = 154 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_6 : (List.finRange 2058).countP
    (fun v => decide (perm 6 v = v)) = 154 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_7 : (List.finRange 2058).countP
    (fun v => decide (perm 7 v = v)) = 154 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_8 : (List.finRange 2058).countP
    (fun v => decide (perm 8 v = v)) = 42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_9 : (List.finRange 2058).countP
    (fun v => decide (perm 9 v = v)) = 154 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_10 : (List.finRange 2058).countP
    (fun v => decide (perm 10 v = v)) = 42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_11 : (List.finRange 2058).countP
    (fun v => decide (perm 11 v = v)) = 154 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_12 : (List.finRange 2058).countP
    (fun v => decide (perm 12 v = v)) = 154 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_13 : (List.finRange 2058).countP
    (fun v => decide (perm 13 v = v)) = 154 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_14 : (List.finRange 2058).countP
    (fun v => decide (perm 14 v = v)) = 154 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_15 : (List.finRange 2058).countP
    (fun v => decide (perm 15 v = v)) = 154 := by decide +kernel

theorem fixed_count (n : Fin 16) : fixedPointCount (element n) = counts n := by
  rw [fixedPointCount_eq _ _ (perm_eq n)]
  fin_cases n
  · exact count_0
  · exact count_1
  · exact count_2
  · exact count_3
  · exact count_4
  · exact count_5
  · exact count_6
  · exact count_7
  · exact count_8
  · exact count_9
  · exact count_10
  · exact count_11
  · exact count_12
  · exact count_13
  · exact count_14
  · exact count_15

private theorem selection (n : Fin 16) : counts n = 42 ↔ n = 2 ∨ n = 8 ∨ n = 10 := by
  have h : ∀ n : Fin 16, counts n = 42 ↔ n = 2 ∨ n = 8 ∨ n = 10 := by
    decide +kernel
  exact h n

set_option maxRecDepth 8192 in
private theorem upper_2_check : ∀ v : Fin 4,
    perm 2 ⟨v.val, by omega⟩ = permProduct 1 [0] ⟨v.val, by omega⟩ := by
  decide +kernel

private theorem upper_2 : element 2 ∈ ambient 1 := by
  have he : element 2 = rowProduct 1 [0] := by
    apply eq_of_four_point_images
    rw [← perm_eq, ← permProduct_eq]
    exact upper_2_check
  rw [he]
  exact rowProduct_mem _ _

set_option maxRecDepth 8192 in
private theorem upper_8_check : ∀ v : Fin 4,
    perm 8 ⟨v.val, by omega⟩ = permProduct 1 [1] ⟨v.val, by omega⟩ := by
  decide +kernel

private theorem upper_8 : element 8 ∈ ambient 1 := by
  have he : element 8 = rowProduct 1 [1] := by
    apply eq_of_four_point_images
    rw [← perm_eq, ← permProduct_eq]
    exact upper_8_check
  rw [he]
  exact rowProduct_mem _ _

set_option maxRecDepth 8192 in
private theorem upper_10_check : ∀ v : Fin 4,
    perm 10 ⟨v.val, by omega⟩ = permProduct 1 [0, 1] ⟨v.val, by omega⟩ := by
  decide +kernel

private theorem upper_10 : element 10 ∈ ambient 1 := by
  have he : element 10 = rowProduct 1 [0, 1] := by
    apply eq_of_four_point_images
    rw [← perm_eq, ← permProduct_eq]
    exact upper_10_check
  rw [he]
  exact rowProduct_mem _ _

set_option maxRecDepth 8192 in
private theorem lower_0_check : ∀ v : Fin 4,
    permProduct 1 [0] ⟨v.val, by omega⟩ =
      (([2] : List (Fin 16)).map perm).prod ⟨v.val, by omega⟩ := by
  decide +kernel

private theorem lower_0 : rowElement 1 0 =
    (([2] : List (Fin 16)).map element).prod := by
  apply eq_of_four_point_images
  rw [← show rowProduct 1 [0] = rowElement 1 0 by simp [rowProduct],
    ← permProduct_eq, map_list_prod, List.map_map]
  simpa only [Function.comp_def, ← perm_eq] using lower_0_check

set_option maxRecDepth 8192 in
private theorem lower_1_check : ∀ v : Fin 4,
    permProduct 1 [1] ⟨v.val, by omega⟩ =
      (([8] : List (Fin 16)).map perm).prod ⟨v.val, by omega⟩ := by
  decide +kernel

private theorem lower_1 : rowElement 1 1 =
    (([8] : List (Fin 16)).map element).prod := by
  apply eq_of_four_point_images
  rw [← show rowProduct 1 [1] = rowElement 1 1 by simp [rowProduct],
    ← permProduct_eq, map_list_prod, List.map_map]
  simpa only [Function.comp_def, ← perm_eq] using lower_1_check

/-- The exact intrinsic signature reconstructs the smaller literal row. -/
theorem reconstruction : fixedPointSpan (ambient 10) 42 = ambient 1 := by
  apply span_eq 10 1 element (fun x hx => (cover x).mp hx)
    (fun x => fixedPointCount x = 42) (fun n => counts n = 42)
  · intro n
    rw [fixed_count]
  · intro n hn
    rcases (selection n).mp hn with rfl | rfl | rfl
    · exact upper_2
    · exact upper_8
    · exact upper_10
  · intro w hw
    have mem_selected (n : Fin 16) (hn : counts n = 42) :
        element n ∈ closure {x | x ∈ ambient 10 ∧ fixedPointCount x = 42} := by
      apply subset_closure
      exact ⟨element_mem n, (fixed_count n).trans hn⟩
    have prod_selected (l : List (Fin 16)) (hl : ∀ n ∈ l, counts n = 42) :
        (l.map element).prod ∈ closure {x | x ∈ ambient 10 ∧ fixedPointCount x = 42} := by
      apply Subgroup.list_prod_mem
      intro x hx
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
      exact mem_selected n (hl n hn)
    simp only [generatorWords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · change rowElement 1 0 ∈ _
      rw [lower_0]
      exact prod_selected [2] (by decide +kernel)
    · change rowElement 1 1 ∈ _
      rw [lower_1]
      exact prod_selected [8] (by decide +kernel)

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.Reconstructions.Row10
