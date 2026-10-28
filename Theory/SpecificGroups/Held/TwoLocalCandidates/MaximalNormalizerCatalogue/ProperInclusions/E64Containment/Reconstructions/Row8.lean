module
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.Reconstructions.FiniteEnumeration

/-!
# Checked enumeration and signatures for Held row 8

Binary products of the literal row generators enumerate this subgroup.
The multiplication table, distinctness, fixed-point counts and the two
span containments are checked in the actual degree-2058 representation.
The four-point base certifies group equalities, while fixed-point counts
check all 2058 vertices. No elementary-abelian hypothesis is assumed.

Sources: ATLAS HeG1-p2058B0, the unchanged catalogue words, GLS3 Table 5.3p.
-/

public section
namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.Reconstructions.Row8
open Subgroup ProperInclusions

@[expose] def indices (n : Fin 8) : List ℕ :=
  ([0, 1, 2] : List ℕ).filter (fun i => n.val / 2 ^ i % 2 == 1)
@[expose] def element (n : Fin 8) : He := rowProduct 8 (indices n)
@[expose] def perm (n : Fin 8) : Equiv.Perm (Fin 2058) := permProduct 8 (indices n)
@[expose] def mulIdx (n m : Fin 8) : Fin 8 := Fin.ofNat 8 (n.val ^^^ m.val)
@[expose] def counts (n : Fin 8) : ℕ := ([2058, 42, 154, 154, 154, 154, 42, 42] : List ℕ)[n.val]?.getD 0

theorem perm_eq (n : Fin 8) : perm n = representation (element n) := permProduct_eq _ _
theorem element_mem (n : Fin 8) : element n ∈ ambient 8 := rowProduct_mem _ _
theorem element_zero : element 0 = 1 := rfl

set_option maxRecDepth 8192 in
private theorem mul_check : ∀ n m : Fin 8, ∀ v : Fin 4,
    (perm n * perm m) ⟨v.val, by omega⟩ = perm (mulIdx n m) ⟨v.val, by omega⟩ := by
  decide +kernel

theorem element_mul (n m : Fin 8) : element n * element m = element (mulIdx n m) := by
  apply eq_of_four_point_images
  simp only [map_mul, ← perm_eq]
  exact mul_check n m

set_option maxRecDepth 8192 in
private theorem injective_check : ∀ n m : Fin 8, perm n 0 = perm m 0 → n = m := by
  decide +kernel

theorem element_injective : Function.Injective element := by
  intro n m he
  apply injective_check
  simp only [perm_eq, he]

@[expose] def generatorIndex (i : Fin 7) : Fin 8 :=
  Fin.ofNat 8 (([1, 2, 4, 3, 5, 7, 6] : List ℕ)[i.val]?.getD 0)

set_option maxRecDepth 8192 in
private theorem generator_check : ∀ i : Fin 7, ∀ v : Fin 4,
    perm (generatorIndex i) ⟨v.val, by omega⟩ =
      permProduct 8 [i.val] ⟨v.val, by omega⟩ := by
  decide +kernel

theorem generator_eq (i : Fin 7) : element (generatorIndex i) = rowElement 8 i.val := by
  apply eq_of_four_point_images
  rw [← perm_eq, ← show rowProduct 8 [i.val] = rowElement 8 i.val by simp [rowProduct],
    ← permProduct_eq]
  exact generator_check i

theorem cover (x : He) : x ∈ ambient 8 ↔ ∃ n : Fin 8, element n = x := by
  apply enumeration 8 element element_mem ⟨0, element_zero⟩
  · intro n m
    exact ⟨mulIdx n m, element_mul n m⟩
  · intro n
    refine ⟨n, inv_eq_of_mul_eq_one_right ?_⟩
    rw [element_mul]
    have h : mulIdx n n = 0 := by simp [mulIdx]
    rw [h, element_zero]
  · intro w hw
    simp only [generatorWords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨generatorIndex 0, generator_eq 0⟩
    · exact ⟨generatorIndex 1, generator_eq 1⟩
    · exact ⟨generatorIndex 2, generator_eq 2⟩
    · exact ⟨generatorIndex 3, generator_eq 3⟩
    · exact ⟨generatorIndex 4, generator_eq 4⟩
    · exact ⟨generatorIndex 5, generator_eq 5⟩
    · exact ⟨generatorIndex 6, generator_eq 6⟩

set_option maxRecDepth 8192 in
private theorem count_0 : (List.finRange 2058).countP
    (fun v => decide (perm 0 v = v)) = 2058 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_1 : (List.finRange 2058).countP
    (fun v => decide (perm 1 v = v)) = 42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_2 : (List.finRange 2058).countP
    (fun v => decide (perm 2 v = v)) = 154 := by decide +kernel

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
    (fun v => decide (perm 6 v = v)) = 42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_7 : (List.finRange 2058).countP
    (fun v => decide (perm 7 v = v)) = 42 := by decide +kernel

theorem fixed_count (n : Fin 8) : fixedPointCount (element n) = counts n := by
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

private theorem selection (n : Fin 8) : counts n = 42 ↔ n = 1 ∨ n = 6 ∨ n = 7 := by
  have h : ∀ n : Fin 8, counts n = 42 ↔ n = 1 ∨ n = 6 ∨ n = 7 := by
    decide +kernel
  exact h n

set_option maxRecDepth 8192 in
private theorem upper_1_check : ∀ v : Fin 4,
    perm 1 ⟨v.val, by omega⟩ = permProduct 3 [1] ⟨v.val, by omega⟩ := by
  decide +kernel

private theorem upper_1 : element 1 ∈ ambient 3 := by
  have he : element 1 = rowProduct 3 [1] := by
    apply eq_of_four_point_images
    rw [← perm_eq, ← permProduct_eq]
    exact upper_1_check
  rw [he]
  exact rowProduct_mem _ _

set_option maxRecDepth 8192 in
private theorem upper_6_check : ∀ v : Fin 4,
    perm 6 ⟨v.val, by omega⟩ = permProduct 3 [0] ⟨v.val, by omega⟩ := by
  decide +kernel

private theorem upper_6 : element 6 ∈ ambient 3 := by
  have he : element 6 = rowProduct 3 [0] := by
    apply eq_of_four_point_images
    rw [← perm_eq, ← permProduct_eq]
    exact upper_6_check
  rw [he]
  exact rowProduct_mem _ _

set_option maxRecDepth 8192 in
private theorem upper_7_check : ∀ v : Fin 4,
    perm 7 ⟨v.val, by omega⟩ = permProduct 3 [0, 1] ⟨v.val, by omega⟩ := by
  decide +kernel

private theorem upper_7 : element 7 ∈ ambient 3 := by
  have he : element 7 = rowProduct 3 [0, 1] := by
    apply eq_of_four_point_images
    rw [← perm_eq, ← permProduct_eq]
    exact upper_7_check
  rw [he]
  exact rowProduct_mem _ _

set_option maxRecDepth 8192 in
private theorem lower_0_check : ∀ v : Fin 4,
    permProduct 3 [0] ⟨v.val, by omega⟩ =
      (([6] : List (Fin 8)).map perm).prod ⟨v.val, by omega⟩ := by
  decide +kernel

private theorem lower_0 : rowElement 3 0 =
    (([6] : List (Fin 8)).map element).prod := by
  apply eq_of_four_point_images
  rw [← show rowProduct 3 [0] = rowElement 3 0 by simp [rowProduct],
    ← permProduct_eq, map_list_prod, List.map_map]
  simpa only [Function.comp_def, ← perm_eq] using lower_0_check

set_option maxRecDepth 8192 in
private theorem lower_1_check : ∀ v : Fin 4,
    permProduct 3 [1] ⟨v.val, by omega⟩ =
      (([1] : List (Fin 8)).map perm).prod ⟨v.val, by omega⟩ := by
  decide +kernel

private theorem lower_1 : rowElement 3 1 =
    (([1] : List (Fin 8)).map element).prod := by
  apply eq_of_four_point_images
  rw [← show rowProduct 3 [1] = rowElement 3 1 by simp [rowProduct],
    ← permProduct_eq, map_list_prod, List.map_map]
  simpa only [Function.comp_def, ← perm_eq] using lower_1_check

/-- The exact intrinsic signature reconstructs the smaller literal row. -/
theorem reconstruction : fixedPointSpan (ambient 8) 42 = ambient 3 := by
  apply span_eq 8 3 element (fun x hx => (cover x).mp hx)
    (fun x => fixedPointCount x = 42) (fun n => counts n = 42)
  · intro n
    rw [fixed_count]
  · intro n hn
    rcases (selection n).mp hn with rfl | rfl | rfl
    · exact upper_1
    · exact upper_6
    · exact upper_7
  · intro w hw
    have mem_selected (n : Fin 8) (hn : counts n = 42) :
        element n ∈ closure {x | x ∈ ambient 8 ∧ fixedPointCount x = 42} := by
      apply subset_closure
      exact ⟨element_mem n, (fixed_count n).trans hn⟩
    have prod_selected (l : List (Fin 8)) (hl : ∀ n ∈ l, counts n = 42) :
        (l.map element).prod ∈ closure {x | x ∈ ambient 8 ∧ fixedPointCount x = 42} := by
      apply Subgroup.list_prod_mem
      intro x hx
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
      exact mem_selected n (hl n hn)
    simp only [generatorWords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · change rowElement 3 0 ∈ _
      rw [lower_0]
      exact prod_selected [6] (by decide +kernel)
    · change rowElement 3 1 ∈ _
      rw [lower_1]
      exact prod_selected [1] (by decide +kernel)

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.Reconstructions.Row8
