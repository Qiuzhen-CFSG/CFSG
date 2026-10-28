module

public import Theory.Character.AlternatingSix.Rational.Permutations

/-!
# Certified rational A6 permutation calculations

The fixed-point, pair and triple counts give the four integer rows defined in
`Permutations`. We certify their squared sums and their values on every element
of orders two, three, four and five, using the natural fixed-point marking for
the two order-three columns.

Mathlib's exhaustive permutation list splits into thirty blocks of 24 elements,
indexed by the first two swap choices. Kernel-checked decisions establish the
four norm subtotals and the power-test count formulas in each block. The list's
coverage and absence of repetitions transfer these calculations to the literal
alternating group and its existing `Fintype` instance. No representation or
conjugacy-separation premise enters the calculation.

Source: Janko, *A characterization of the Mathieu simple groups, I*, Section 6,
pp.10–11, the rational A6 rows of degrees 9, 10, 5 and 5.
-/

open scoped BigOperators

namespace Theory.Character.AlternatingSix.RationalConstruction

open Equiv Equiv.Perm

private abbrev S6 := Perm (Fin 6)
private def evenSquare (j : Fin 4) (g : S6) : ℤ :=
  if h : sign g = 1 then rowValues j ⟨g,h⟩ ^ 2 else 0
-- Each subtotal is checked on the 24 permutations of the last four letters.
private def blockSums : Fin 6 → Fin 5 → Fin 4 → ℤ :=
  ![![![84, 120, 60, 36], ![9, 15, 15, 6], ![9, 15, 15, 6], ![9, 15, 15, 6], ![9, 15, 15, 6]],
    ![![12, 24, 12, 12], ![9, 3, 9, 12], ![9, 3, 9, 12], ![9, 3, 9, 12], ![9, 3, 9, 12]],
    ![![9, 15, 15, 6], ![9, 3, 9, 12], ![10, 6, 8, 14], ![10, 6, 8, 14], ![10, 6, 8, 14]],
    ![![9, 15, 15, 6], ![10, 6, 8, 14], ![9, 3, 9, 12], ![10, 6, 8, 14], ![10, 6, 8, 14]],
    ![![9, 15, 15, 6], ![10, 6, 8, 14], ![10, 6, 8, 14], ![9, 3, 9, 12], ![10, 6, 8, 14]],
    ![![9, 15, 15, 6], ![10, 6, 8, 14], ![10, 6, 8, 14], ![10, 6, 8, 14], ![9, 3, 9, 12]]]
private def normBlock (i : Fin 6) (j : Fin 5) (k : Fin 4) : ℤ :=
  ((permsOfList ([2, 3, 4, 5] : List (Fin 6))).map
    (fun g => evenSquare k (swap 0 i * swap 1 j.succ * g))).sum
-- Each declaration checks only one of the six first-swap blocks.
private theorem normBlocks_0 (j : Fin 5) (k : Fin 4) :
    normBlock 0 j k = blockSums 0 j k := by
  fin_cases j <;> fin_cases k <;> decide +kernel

private theorem normBlocks_1 (j : Fin 5) (k : Fin 4) :
    normBlock 1 j k = blockSums 1 j k := by
  fin_cases j <;> fin_cases k <;> decide +kernel

private theorem normBlocks_2 (j : Fin 5) (k : Fin 4) :
    normBlock 2 j k = blockSums 2 j k := by
  fin_cases j <;> fin_cases k <;> decide +kernel

private theorem normBlocks_3 (j : Fin 5) (k : Fin 4) :
    normBlock 3 j k = blockSums 3 j k := by
  fin_cases j <;> fin_cases k <;> decide +kernel

private theorem normBlocks_4 (j : Fin 5) (k : Fin 4) :
    normBlock 4 j k = blockSums 4 j k := by
  fin_cases j <;> fin_cases k <;> decide +kernel

private theorem normBlocks_5 (j : Fin 5) (k : Fin 4) :
    normBlock 5 j k = blockSums 5 j k := by
  fin_cases j <;> fin_cases k <;> decide +kernel

private theorem normBlocks (i : Fin 6) (j : Fin 5) (k : Fin 4) :
    normBlock i j k = blockSums i j k := by
  fin_cases i
  · exact normBlocks_0 j k
  · exact normBlocks_1 j k
  · exact normBlocks_2 j k
  · exact normBlocks_3 j k
  · exact normBlocks_4 j k
  · exact normBlocks_5 j k

private theorem sum_perms_cons (a : Fin 6) (l : List (Fin 6)) (f : S6 → ℤ) :
    ((permsOfList (a :: l)).map f).sum =
      ((a :: l).map fun b => ((permsOfList l).map fun g => f (swap a b * g)).sum).sum := by
  simp [permsOfList, List.flatMap, List.sum_flatten,
    List.map_map, Function.comp_def, ← Equiv.Perm.one_def]

private theorem list_norm (k : Fin 4) :
    ((permsOfList ([0, 1, 2, 3, 4, 5] : List (Fin 6))).map (evenSquare k)).sum = 360 := by
  rw [sum_perms_cons]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp_rw [sum_perms_cons 1 [2, 3, 4, 5]]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [← mul_assoc]
  change (List.ofFn (fun i : Fin 6 =>
    (List.ofFn fun j : Fin 5 => normBlock i j k).sum)).sum = 360
  simp_rw [normBlocks]
  fin_cases k <;> decide +kernel

private theorem norm_square_sum (k : Fin 4) : ∑ g : A6, rowValues k g ^ 2 = 360 := by
  classical
  have hu : (permsOfList ([0, 1, 2, 3, 4, 5] : List (Fin 6))).toFinset =
      (Finset.univ : Finset S6) := by
    ext g
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    apply mem_permsOfList_of_mem
    intro x _
    fin_cases x <;> simp
  have h := list_norm k
  rw [← List.sum_toFinset _ (nodup_permsOfList (by decide)), hu] at h
  have hs : (∑ g : S6, evenSquare k g) = ∑ g : A6, rowValues k g ^ 2 := by
    calc
      (∑ g : S6, evenSquare k g) =
          ∑ g ∈ Finset.univ.filter (fun g : S6 => sign g = 1), evenSquare k g := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro g _
        by_cases hg : sign g = 1 <;> simp [evenSquare, hg]
      _ = ∑ g : A6, evenSquare k g.val :=
        Finset.sum_subtype _ (by intro g; simp [mem_alternatingGroup]) _
      _ = ∑ g : A6, rowValues k g ^ 2 := by
        apply Finset.sum_congr rfl
        intro g _
        exact dif_pos (show sign g.val = 1 from g.property)
  exact hs ▸ h

-- Power tests are computable; the assembly below derives them from exact orders.
private def countsCheck (g : S6) : Prop :=
  if h : sign g = 1 then
    let x : A6 := ⟨g, h⟩
    (x ^ 2 = 1 → x ≠ 1 →
      pointCount x = 2 ∧ subsetCount 2 x = 3 ∧ subsetCount 3 x = 4) ∧
    (x ^ 3 = 1 → x ≠ 1 →
      (pointCount x = 3 ∧ subsetCount 2 x = 3 ∧ subsetCount 3 x = 2) ∨
      (pointCount x = 0 ∧ subsetCount 2 x = 0 ∧ subsetCount 3 x = 2)) ∧
    (x ^ 4 = 1 → x ^ 2 ≠ 1 →
      pointCount x = 0 ∧ subsetCount 2 x = 1 ∧ subsetCount 3 x = 0) ∧
    (x ^ 5 = 1 → x ≠ 1 →
      pointCount x = 1 ∧ subsetCount 2 x = 0 ∧ subsetCount 3 x = 0)
  else True
-- Assemble the four decision procedures separately to keep instance search small.
private instance (g : S6) : Decidable (countsCheck g) := by
  unfold countsCheck
  split
  · dsimp only
    refine @instDecidableAnd _ _ ?_ ?_
    · infer_instance
    · refine @instDecidableAnd _ _ ?_ ?_
      · infer_instance
      · refine @instDecidableAnd _ _ ?_ ?_ <;> infer_instance
  · infer_instance

private def countsBlock (i : Fin 6) (j : Fin 5) : Prop :=
  ∀ g ∈ permsOfList ([2, 3, 4, 5] : List (Fin 6)),
    countsCheck (swap 0 i * swap 1 j.succ * g)
-- Use list-bounded quantification, without enumerating S6 to test list membership.
private instance (i : Fin 6) (j : Fin 5) : Decidable (countsBlock i j) :=
  List.decidableBAll _ _
private theorem countsBlocks (i : Fin 6) (j : Fin 5) : countsBlock i j := by
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem split_perms {i : Fin 6} {l : List (Fin 6)} (a : S6)
    (ha : a ∈ permsOfList (i :: l)) :
    ∃ j ∈ i :: l, ∃ b ∈ permsOfList l, a = swap i j * b := by
  rw [permsOfList] at ha
  rcases List.mem_append.mp ha with h | h
  · exact ⟨i, by simp, a, h, by rw [swap_self]; rfl⟩
  · obtain ⟨j, hj, hj'⟩ := List.mem_flatMap.mp h
    obtain ⟨b, hb, hba⟩ := List.mem_map.mp hj'
    exact ⟨j, List.mem_cons_of_mem _ hj, b, hb, hba.symm⟩

private theorem counts_all (g : S6) : countsCheck g := by
  have hg : g ∈ permsOfList ([0, 1, 2, 3, 4, 5] : List (Fin 6)) :=
    mem_permsOfList_of_mem (by intro x _; fin_cases x <;> simp)
  obtain ⟨i, _, b, hb, hab⟩ := split_perms g hg
  obtain ⟨j, hj, c, hc, hbc⟩ := split_perms b hb
  have hj0 : j ≠ 0 := by intro h; subst j; simp at hj
  obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hj0
  rw [hab, hbc, ← mul_assoc]
  exact countsBlocks i k c hc

private theorem values_two (j : Fin 4) (x : A6) (hx : orderOf x = 2) :
    rowValues j x = rationalValues j 1 := by
  have h := counts_all x.val
  simp only [countsCheck, show sign x.val = 1 from x.property, dif_pos] at h
  have hp : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
  have hn : x ≠ 1 := by intro hn; simp [hn] at hx
  obtain ⟨h1, h2, h3⟩ := h.1 hp hn
  fin_cases j <;> norm_num [rowValues, rationalValues, h1, h2, h3]

private theorem values_three (j : Fin 4) (x : A6) (hx : orderOf x = 3) :
    rowValues j x = rationalValues j (if pointCount x = 3 then 2 else 3) := by
  have h := counts_all x.val
  simp only [countsCheck, show sign x.val = 1 from x.property, dif_pos] at h
  have hp : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have hn : x ≠ 1 := by intro hn; simp [hn] at hx
  rcases h.2.1 hp hn with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
    fin_cases j <;> norm_num [rowValues, rationalValues, h1, h2, h3] <;> rfl

private theorem values_four (j : Fin 4) (x : A6) (hx : orderOf x = 4) :
    rowValues j x = rationalValues j 4 := by
  have h := counts_all x.val
  simp only [countsCheck, show sign x.val = 1 from x.property, dif_pos] at h
  have hp : x ^ 4 = 1 := hx ▸ pow_orderOf_eq_one x
  have hn : x ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by decide) (by omega)
  obtain ⟨h1, h2, h3⟩ := h.2.2.1 hp hn
  fin_cases j <;> norm_num [rowValues, rationalValues, h1, h2, h3] <;> rfl

private theorem values_five (j : Fin 4) (x : A6) (hx : orderOf x = 5) :
    rowValues j x = rationalValues j 5 := by
  have h := counts_all x.val
  simp only [countsCheck, show sign x.val = 1 from x.property, dif_pos] at h
  have hp : x ^ 5 = 1 := hx ▸ pow_orderOf_eq_one x
  have hn : x ≠ 1 := by intro hn; simp [hn] at hx
  obtain ⟨h1, h2, h3⟩ := h.2.2.2 hp hn
  fin_cases j <;> norm_num [rowValues, rationalValues, h1, h2, h3] <;> rfl

set_option linter.defProp false in
/-- The finite calculations for the four rational permutation-character rows,
with no additional character-theoretic or conjugacy assumptions. -/
public def permutationCalculations : PermutationCalculations where
  square_sum := norm_square_sum
  two := values_two
  three := values_three
  four := values_four
  five := values_five

end Theory.Character.AlternatingSix.RationalConstruction
