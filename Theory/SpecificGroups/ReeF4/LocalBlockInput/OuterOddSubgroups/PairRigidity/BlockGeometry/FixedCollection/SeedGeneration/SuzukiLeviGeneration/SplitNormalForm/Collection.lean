module
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.SuzukiLeviGeneration.Basic
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.SuzukiCoordinates.SplitBlock
public import Theory.GroupTheory.FilteredCollection

/-!
# Collection within the four-root B₂ block

The checked B₂ matrix exchanges put any partition of the four positive root
curves in the chosen order. Their two correction curves are central, giving
a two-step filtration. The four-parameter coverage theorem supplies a word
for every element of the actual generated positive block.

Source: GLS3 1.11.5, 1.12.1, and Table 2.4 type V,
`refs/KGroup/GLS3/Chapter1.tex` and `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Subgroup LargeLocalSeeds BlockParameters.FieldRecovery.SuzukiChart FilteredCollection
namespace SuzukiSplitNormalForm
variable {m : ℕ}

private theorem swap_reverse (a b : CoefficientField m) :
    X 0 a * X 1 b = X 1 b * X 0 a * X 2 (a * b) * X 3 (a * b ^ 2) := by
  have hE : (X 2 (a * b) * X 3 (a * b ^ 2)) *
      (X 2 (a * b) * X 3 (a * b ^ 2)) = 1 := by
    rw [(commute23 (a * b) (a * b ^ 2)).symm.mul_mul_mul_comm, X_self, X_self, one_mul]
  have h := congrArg (fun z => z * (X 2 (a * b) * X 3 (a * b ^ 2))) (swap a b)
  have he := hE
  simp only [mul_assoc] at he
  simpa only [mul_assoc, he, mul_one] using h.symm

private theorem exchanges (i j : Fin 4) (a b : CoefficientField m) (hne : i ≠ j) :
    ∃ c : List (Fin 4 × CoefficientField m),
      (∀ z ∈ c, max (if i < 2 then 0 else 1) (if j < 2 then 0 else 1) <
        (if z.1 < 2 then 0 else 1)) ∧
      X i a * X j b = X j b * X i a * wordProduct (X (m := m)) c := by
  fin_cases i <;> fin_cases j
  all_goals try exact (hne rfl).elim
  · refine ⟨[(2, a * b), (3, a * b ^ 2)], ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro z (rfl | rfl) <;> change (0 : ℕ) < 1 <;> decide
    · simpa [wordProduct, mul_assoc] using swap_reverse a b
  · exact ⟨[], by simp, by simpa [wordProduct] using (commute02 a b).eq⟩
  · exact ⟨[], by simp, by simpa [wordProduct] using (commute03 a b).eq⟩
  · refine ⟨[(2, b * a), (3, b * a ^ 2)], ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro z (rfl | rfl) <;> change (0 : ℕ) < 1 <;> decide
    · simpa [wordProduct, mul_assoc] using swap b a
  · exact ⟨[], by simp, by simpa [wordProduct] using (commute12 a b).eq⟩
  · exact ⟨[], by simp, by simpa [wordProduct] using (commute13 a b).eq⟩
  · exact ⟨[], by simp, by simpa [wordProduct] using (commute02 b a).symm.eq⟩
  · exact ⟨[], by simp, by simpa [wordProduct] using (commute12 b a).symm.eq⟩
  · exact ⟨[], by simp, by simpa [wordProduct] using (commute23 a b).eq⟩
  · exact ⟨[], by simp, by simpa [wordProduct] using (commute03 b a).symm.eq⟩
  · exact ⟨[], by simp, by simpa [wordProduct] using (commute13 b a).symm.eq⟩
  · exact ⟨[], by simp, by simpa [wordProduct] using (commute23 b a).symm.eq⟩

/-- Partition collection stays inside the actual four-root positive Levi block. -/
theorem positive_factorization (A B : Subgroup (SplitGroup m))
    (hroot : ∀ i : Fin 4, (∀ t, X i t ∈ A) ∨ (∀ t, X i t ∈ B))
    {u : SplitGroup m} (hu : u ∈ splitSimpleBlock m .suzuki true) :
    ∃ a ∈ A, ∃ b ∈ B, u = a * b := by
  classical
  let roots := (Finset.univ : Finset (Fin 4)).toList
  let p : Fin 4 → Prop := fun r => ∀ t, X r t ∈ A
  let left := roots.filter (fun r => decide (p r))
  let right := roots.filter (fun r => decide (¬ p r))
  let order := left ++ right
  have hmem (r : Fin 4) : r ∈ order := by
    simp only [order, left, right, List.mem_append, List.mem_filter, decide_eq_true_eq]
    have hr : r ∈ roots := by simp [roots]
    by_cases h : p r
    · exact Or.inl ⟨hr, h⟩
    · exact Or.inr ⟨hr, h⟩
  have hnd : order.Nodup := by
    apply List.nodup_append.mpr
    refine ⟨List.Nodup.filter _ (Finset.nodup_toList _),
      List.Nodup.filter _ (Finset.nodup_toList _), ?_⟩
    intro a ha b hb hab
    subst b
    exact (of_decide_eq_true (List.mem_filter.mp hb).2)
      (of_decide_eq_true (List.mem_filter.mp ha).2)
  obtain ⟨q, rfl⟩ := splitWord_cover hu
  obtain ⟨t, ht⟩ := filteredCollection_exists_params
    (fun i : Fin 4 => if i < 2 then 0 else 1) (X (m := m)) order hnd 2
    (fun i _ => by split <;> omega) (fun i a b => (X_add i a b).symm)
    (fun i j a b _ _ hne => by
      obtain ⟨c, hc, he⟩ := exchanges i j a b hne
      exact ⟨c, fun z hz => ⟨hmem z.1, hc z hz⟩, he⟩)
    [(0, q 0), (1, q 1), (2, q 2), (3, q 3)] (fun z _ => hmem z.1)
  refine ⟨(left.map fun r => X r (t r)).prod, ?_,
    (right.map fun r => X r (t r)).prod, ?_, ?_⟩
  · apply A.list_prod_mem
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    exact (of_decide_eq_true (List.mem_filter.mp hr).2) (t r)
  · apply B.list_prod_mem
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    exact ((hroot r).resolve_left (of_decide_eq_true (List.mem_filter.mp hr).2)) (t r)
  · simpa only [splitWord_def, wordProduct, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, order, List.map_append, List.prod_append,
      mul_assoc] using ht
end SuzukiSplitNormalForm
end ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
