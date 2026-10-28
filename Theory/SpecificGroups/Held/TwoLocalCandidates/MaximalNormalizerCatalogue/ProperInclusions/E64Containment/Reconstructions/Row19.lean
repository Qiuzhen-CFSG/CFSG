module
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.Reconstructions.FiniteEnumeration

/-!
# Checked enumeration and signatures for Held row 19

Binary products of the literal row generators enumerate this subgroup.
The multiplication table, distinctness, fixed-point counts and the two
span containments are checked in the actual degree-2058 representation.
The four-point base certifies group equalities, while fixed-point counts
check all 2058 vertices. No elementary-abelian hypothesis is assumed.

Sources: ATLAS HeG1-p2058B0, the unchanged catalogue words, GLS3 Table 5.3p.
-/

public section
namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.Reconstructions.Row19
open Subgroup ProperInclusions

@[expose] def indices (n : Fin 32) : List ℕ :=
  ([0, 1, 2, 3, 4] : List ℕ).filter (fun i => n.val / 2 ^ i % 2 == 1)
@[expose] def element (n : Fin 32) : He := rowProduct 19 (indices n)
@[expose] def perm (n : Fin 32) : Equiv.Perm (Fin 2058) := permProduct 19 (indices n)
@[expose] def mulIdx (n m : Fin 32) : Fin 32 := Fin.ofNat 32 (n.val ^^^ m.val)
@[expose] def counts (n : Fin 32) : ℕ := ([2058, 42, 42, 154, 154, 42, 42, 42, 154, 42, 154, 42, 42, 42, 42, 42, 42, 42, 42, 42, 154, 154, 42, 42, 154, 154, 154, 42, 42, 42, 42, 154] : List ℕ)[n.val]?.getD 0

theorem perm_eq (n : Fin 32) : perm n = representation (element n) := permProduct_eq _ _
theorem element_mem (n : Fin 32) : element n ∈ ambient 19 := rowProduct_mem _ _
theorem element_zero : element 0 = 1 := rfl

set_option maxRecDepth 8192 in
private theorem mul_check : ∀ n m : Fin 32, ∀ v : Fin 4,
    (perm n * perm m) ⟨v.val, by omega⟩ = perm (mulIdx n m) ⟨v.val, by omega⟩ := by
  decide +kernel

theorem element_mul (n m : Fin 32) : element n * element m = element (mulIdx n m) := by
  apply eq_of_four_point_images
  simp only [map_mul, ← perm_eq]
  exact mul_check n m

set_option maxRecDepth 8192 in
private theorem injective_check : ∀ n m : Fin 32,
    (∀ v : Fin 4, perm n ⟨v.val, by omega⟩ = perm m ⟨v.val, by omega⟩) → n = m := by
  decide +kernel

theorem element_injective : Function.Injective element := by
  intro n m he
  apply injective_check
  intro v
  simp only [perm_eq, he]

@[expose] def generatorIndex (i : Fin 5) : Fin 32 :=
  Fin.ofNat 32 (([1, 2, 4, 8, 16] : List ℕ)[i.val]?.getD 0)

set_option maxRecDepth 8192 in
private theorem generator_check : ∀ i : Fin 5, ∀ v : Fin 4,
    perm (generatorIndex i) ⟨v.val, by omega⟩ =
      permProduct 19 [i.val] ⟨v.val, by omega⟩ := by
  decide +kernel

theorem generator_eq (i : Fin 5) : element (generatorIndex i) = rowElement 19 i.val := by
  apply eq_of_four_point_images
  rw [← perm_eq, ← show rowProduct 19 [i.val] = rowElement 19 i.val by simp [rowProduct],
    ← permProduct_eq]
  exact generator_check i

theorem cover (x : He) : x ∈ ambient 19 ↔ ∃ n : Fin 32, element n = x := by
  apply enumeration 19 element element_mem ⟨0, element_zero⟩
  · intro n m
    exact ⟨mulIdx n m, element_mul n m⟩
  · intro n
    refine ⟨n, inv_eq_of_mul_eq_one_right ?_⟩
    rw [element_mul]
    have h : mulIdx n n = 0 := by simp [mulIdx]
    rw [h, element_zero]
  · intro w hw
    simp only [generatorWords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact ⟨generatorIndex 0, generator_eq 0⟩
    · exact ⟨generatorIndex 1, generator_eq 1⟩
    · exact ⟨generatorIndex 2, generator_eq 2⟩
    · exact ⟨generatorIndex 3, generator_eq 3⟩
    · exact ⟨generatorIndex 4, generator_eq 4⟩

attribute [local irreducible] perm permProduct

set_option maxRecDepth 8192 in
private theorem count_0 : (List.finRange 2058).countP
    (fun v => decide (perm 0 v = v)) = 2058 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_1 : (List.finRange 2058).countP
    (fun v => decide (perm 1 v = v)) = 42 := by decide +kernel

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
    (fun v => decide (perm 5 v = v)) = 42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_6 : (List.finRange 2058).countP
    (fun v => decide (perm 6 v = v)) = 42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_7 : (List.finRange 2058).countP
    (fun v => decide (perm 7 v = v)) = 42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_8 : (List.finRange 2058).countP
    (fun v => decide (perm 8 v = v)) = 154 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_9 : (List.finRange 2058).countP
    (fun v => decide (perm 9 v = v)) = 42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_10 : (List.finRange 2058).countP
    (fun v => decide (perm 10 v = v)) = 154 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_11 : (List.finRange 2058).countP
    (fun v => decide (perm 11 v = v)) = 42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_12 : (List.finRange 2058).countP
    (fun v => decide (perm 12 v = v)) = 42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_13 : (List.finRange 2058).countP
    (fun v => decide (perm 13 v = v)) = 42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_14 : (List.finRange 2058).countP
    (fun v => decide (perm 14 v = v)) = 42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_15 : (List.finRange 2058).countP
    (fun v => decide (perm 15 v = v)) = 42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_16 : (List.finRange 2058).countP
    (fun v => decide (perm 16 v = v)) = 42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_17 : (List.finRange 2058).countP
    (fun v => decide (perm 17 v = v)) = 42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_18 : (List.finRange 2058).countP
    (fun v => decide (perm 18 v = v)) = 42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_19 : (List.finRange 2058).countP
    (fun v => decide (perm 19 v = v)) = 42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_20 : (List.finRange 2058).countP
    (fun v => decide (perm 20 v = v)) = 154 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_21 : (List.finRange 2058).countP
    (fun v => decide (perm 21 v = v)) = 154 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_22 : (List.finRange 2058).countP
    (fun v => decide (perm 22 v = v)) = 42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_23 : (List.finRange 2058).countP
    (fun v => decide (perm 23 v = v)) = 42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_24 : (List.finRange 2058).countP
    (fun v => decide (perm 24 v = v)) = 154 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_25 : (List.finRange 2058).countP
    (fun v => decide (perm 25 v = v)) = 154 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_26 : (List.finRange 2058).countP
    (fun v => decide (perm 26 v = v)) = 154 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_27 : (List.finRange 2058).countP
    (fun v => decide (perm 27 v = v)) = 42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_28 : (List.finRange 2058).countP
    (fun v => decide (perm 28 v = v)) = 42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_29 : (List.finRange 2058).countP
    (fun v => decide (perm 29 v = v)) = 42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_30 : (List.finRange 2058).countP
    (fun v => decide (perm 30 v = v)) = 42 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem count_31 : (List.finRange 2058).countP
    (fun v => decide (perm 31 v = v)) = 154 := by decide +kernel

theorem fixed_count (n : Fin 32) : fixedPointCount (element n) = counts n := by
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
  · exact count_16
  · exact count_17
  · exact count_18
  · exact count_19
  · exact count_20
  · exact count_21
  · exact count_22
  · exact count_23
  · exact count_24
  · exact count_25
  · exact count_26
  · exact count_27
  · exact count_28
  · exact count_29
  · exact count_30
  · exact count_31

@[expose] def overlaps (n : Fin 32) : ℕ := ([10, 4, 4, 2, 0, 2, 2, 4, 0, 2, 2, 4, 6, 4, 4, 2, 6, 4, 4, 2, 0, 2, 2, 4, 0, 2, 2, 4, 6, 4, 4, 2] : List ℕ)[n.val]?.getD 0

private theorem overlap_check : ∀ n : Fin 32, (List.finRange 32).countP
    (fun k => decide (counts k = 154 ∧ counts (mulIdx n k) = 154)) = overlaps n := by
  decide +kernel

theorem overlap_count (n : Fin 32) : overlapCount (ambient 19) (element n) = overlaps n := by
  rw [overlapCount_eq 19 element element_mem element_injective
    (fun x hx => (cover x).mp hx) counts fixed_count mulIdx element_mul n]
  exact overlap_check n

private theorem selection (n : Fin 32) : overlaps n = 6 ↔ n = 12 ∨ n = 16 ∨ n = 28 := by
  have h : ∀ n : Fin 32, overlaps n = 6 ↔ n = 12 ∨ n = 16 ∨ n = 28 := by
    decide +kernel
  exact h n

set_option maxRecDepth 8192 in
private theorem upper_12_check : ∀ v : Fin 4,
    perm 12 ⟨v.val, by omega⟩ = permProduct 3 [0] ⟨v.val, by omega⟩ := by
  decide +kernel

private theorem upper_12 : element 12 ∈ ambient 3 := by
  have he : element 12 = rowProduct 3 [0] := by
    apply eq_of_four_point_images
    rw [← perm_eq, ← permProduct_eq]
    exact upper_12_check
  rw [he]
  exact rowProduct_mem _ _

set_option maxRecDepth 8192 in
private theorem upper_16_check : ∀ v : Fin 4,
    perm 16 ⟨v.val, by omega⟩ = permProduct 3 [1] ⟨v.val, by omega⟩ := by
  decide +kernel

private theorem upper_16 : element 16 ∈ ambient 3 := by
  have he : element 16 = rowProduct 3 [1] := by
    apply eq_of_four_point_images
    rw [← perm_eq, ← permProduct_eq]
    exact upper_16_check
  rw [he]
  exact rowProduct_mem _ _

set_option maxRecDepth 8192 in
private theorem upper_28_check : ∀ v : Fin 4,
    perm 28 ⟨v.val, by omega⟩ = permProduct 3 [0, 1] ⟨v.val, by omega⟩ := by
  decide +kernel

private theorem upper_28 : element 28 ∈ ambient 3 := by
  have he : element 28 = rowProduct 3 [0, 1] := by
    apply eq_of_four_point_images
    rw [← perm_eq, ← permProduct_eq]
    exact upper_28_check
  rw [he]
  exact rowProduct_mem _ _

set_option maxRecDepth 8192 in
private theorem lower_0_check : ∀ v : Fin 4,
    permProduct 3 [0] ⟨v.val, by omega⟩ =
      (([12] : List (Fin 32)).map perm).prod ⟨v.val, by omega⟩ := by
  decide +kernel

private theorem lower_0 : rowElement 3 0 =
    (([12] : List (Fin 32)).map element).prod := by
  apply eq_of_four_point_images
  rw [← show rowProduct 3 [0] = rowElement 3 0 by simp [rowProduct],
    ← permProduct_eq, map_list_prod, List.map_map]
  simpa only [Function.comp_def, ← perm_eq] using lower_0_check

set_option maxRecDepth 8192 in
private theorem lower_1_check : ∀ v : Fin 4,
    permProduct 3 [1] ⟨v.val, by omega⟩ =
      (([16] : List (Fin 32)).map perm).prod ⟨v.val, by omega⟩ := by
  decide +kernel

private theorem lower_1 : rowElement 3 1 =
    (([16] : List (Fin 32)).map element).prod := by
  apply eq_of_four_point_images
  rw [← show rowProduct 3 [1] = rowElement 3 1 by simp [rowProduct],
    ← permProduct_eq, map_list_prod, List.map_map]
  simpa only [Function.comp_def, ← perm_eq] using lower_1_check

/-- The exact intrinsic signature reconstructs the smaller literal row. -/
theorem reconstruction : overlapSpan (ambient 19) 6 = ambient 3 := by
  apply span_eq 19 3 element (fun x hx => (cover x).mp hx)
    (fun x => overlapCount (ambient 19) x = 6) (fun n => overlaps n = 6)
  · intro n
    rw [overlap_count]
  · intro n hn
    rcases (selection n).mp hn with rfl | rfl | rfl
    · exact upper_12
    · exact upper_16
    · exact upper_28
  · intro w hw
    have mem_selected (n : Fin 32) (hn : overlaps n = 6) :
        element n ∈ closure {x | x ∈ ambient 19 ∧ overlapCount (ambient 19) x = 6} := by
      apply subset_closure
      exact ⟨element_mem n, (overlap_count n).trans hn⟩
    have prod_selected (l : List (Fin 32)) (hl : ∀ n ∈ l, overlaps n = 6) :
        (l.map element).prod ∈ closure {x | x ∈ ambient 19 ∧ overlapCount (ambient 19) x = 6} := by
      apply Subgroup.list_prod_mem
      intro x hx
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
      exact mem_selected n (hl n hn)
    simp only [generatorWords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · change rowElement 3 0 ∈ _
      rw [lower_0]
      exact prod_selected [12] (by decide +kernel)
    · change rowElement 3 1 ∈ _
      rw [lower_1]
      exact prod_selected [16] (by decide +kernel)

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.Reconstructions.Row19
