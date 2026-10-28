module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.SplitNormalForm.Inputs

/-!
# Positive-root partitions for concrete split D4 cells

The established binary Geck exchange identities and the degree-filtered collector
allow any ordering of the twelve positive roots. Putting one part of a partition
first gives two products, each still in the published twelve-root order with
zero coordinates outside its part. Weyl conjugation absorbs the part with
positive images into the positive subgroup. No cell decomposition is assumed.

Source: GLS3 2.3.7–8 and §2.4 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section

open Theory.AlgebraicGroup.StandardRootSystem
open FilteredCollection
namespace Triality.Standard.ConcreteBruhat.SplitNormalForm.CellCollection
open PositiveCoordinates Parabolics
noncomputable section


/-- Collection in any order of the twelve actual positive curves. -/
theorem positive_collected_in_order (n : ℕ) (hn : 0 < n)
    (order : List (Fin 12)) (hnd : order.Nodup) (hall : ∀ i, i ∈ order)
    {u : SplitGroup (binaryParameters n hn)} (hu : u ∈ positiveSubgroup _) :
    ∃ a : PositiveCoordinates.Coordinates (binaryParameters n hn),
      u = (order.map fun i => curve _ i (a i)).prod := by
  classical
  let P := binaryParameters n hn
  have hswap : ∀ (i j : Fin 12) (a b : ExtensionField P),
      i ∈ order → j ∈ order → i ≠ j →
      ∃ correction : List (Fin 12 × ExtensionField P),
        (∀ z ∈ correction, z.1 ∈ order ∧
          max (collectionHeight i) (collectionHeight j) < collectionHeight z.1) ∧
        curve P i a * curve P j b =
          curve P j b * curve P i a * wordProduct (curve P) correction := by
    intro i j a b _ _ hij
    by_cases h : ∃ k : Fin 12, (typeDRootPairing 2).root (rootIndex k) =
        (typeDRootPairing 2).root (rootIndex i) + (typeDRootPairing 2).root (rootIndex j)
    · obtain ⟨k, hk⟩ := h
      refine ⟨[(k, a * b)], ?_, ?_⟩
      · intro z hz
        have hz' : z = (k, a * b) := by simpa using hz
        subst z
        exact ⟨hall k, collectionHeight_sum_gt hk⟩
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one] using sumExchange_binary n hn i j k hk a b
    · refine ⟨[], by simp, ?_⟩
      simpa only [wordProduct, List.map_nil, List.prod_nil, mul_one] using
        (nonsumCommute_binary n hn i j hij h a b).eq
  obtain ⟨word, rfl⟩ := exists_positive_word_of_mem_positiveSubgroup P hu
  exact filteredCollection_exists_params collectionHeight (curve P)
    order hnd 6 (fun i _ => collectionHeight_lt_six i)
    (fun i a b => (curve_add P i a b).symm) hswap word (fun z _ => hall z.1)

private theorem filtered_product (P : Parameters) (p : Fin 12 → Prop) [DecidablePred p]
    (a : PositiveCoordinates.Coordinates P) (l : List (Fin 12)) :
    ((l.filter fun i => decide (p i)).map fun i => curve P i (a i)).prod =
      (l.map fun i => curve P i (if p i then a i else 0)).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    by_cases hi : p i <;> simp [hi, ih]

/-- Partition a positive element into two ordered products, with complementary supports. -/
theorem positive_partition (n : ℕ) (hn : 0 < n) (p : Fin 12 → Prop)
    {u : SplitGroup (binaryParameters n hn)} (hu : u ∈ positiveSubgroup _) :
    ∃ a b : PositiveCoordinates.Coordinates (binaryParameters n hn),
      (∀ i, ¬ p i → a i = 0) ∧ (∀ i, p i → b i = 0) ∧
      u = orderedProduct _ a * orderedProduct _ b := by
  classical
  let l := List.finRange 12
  let l₁ := l.filter fun i => decide (p i)
  let l₂ := l.filter fun i => decide (¬ p i)
  have hnd : (l₁ ++ l₂).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨(List.nodup_finRange 12).filter _, (List.nodup_finRange 12).filter _, ?_⟩
    apply List.disjoint_left.mpr
    intro i hi hj
    have hpi : p i := by simpa [l₁] using (List.mem_filter.mp hi).2
    have hnpi : ¬ p i := by simpa [l₂] using (List.mem_filter.mp hj).2
    exact hnpi hpi
  have hall : ∀ i, i ∈ l₁ ++ l₂ := by
    intro i
    by_cases hi : p i <;> simp [l₁, l₂, l, hi]
  obtain ⟨a, ha⟩ := positive_collected_in_order n hn (l₁ ++ l₂) hnd hall hu
  refine ⟨(fun i => if p i then a i else 0),
    (fun i => if ¬ p i then a i else 0), ?_, ?_, ?_⟩
  · intro i hi
    simp [hi]
  · intro i hi
    simp [hi]
  · simpa only [List.map_append, List.prod_append, l₁, l₂, filtered_product,
      orderedProduct, List.ofFn_eq_map] using ha

private theorem conjugate_list_prod_mem {G : Type*} [Group G] (H : Subgroup G)
    (x : G) (l : List G) (h : ∀ g ∈ l, x * g * x⁻¹ ∈ H) :
    x * l.prod * x⁻¹ ∈ H := by
  induction l with
  | nil => simp
  | cons g l ih =>
    have hg := h g (List.mem_cons_self ..)
    have hl := ih (fun a ha => h a (List.mem_cons_of_mem g ha))
    convert H.mul_mem hg hl using 1
    simp [mul_assoc]

theorem lift_conjugate_root {P : Parameters} (D : Inputs P)
    (w : rootWeylGroup) (r : TypeDRootIndex 4) (t : ExtensionField P) :
    D.lift w * rootCurve P r t * (D.lift w)⁻¹ = rootCurve P (w.val r) t :=
  D.conjugate_root w r t

/-- Conjugation sends a supported ordered product into the positive subgroup
whenever its nonzero roots have positive images. -/
theorem conjugate_orderedProduct_mem_positive (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (w : rootWeylGroup)
    (a : PositiveCoordinates.Coordinates (binaryParameters n hn))
    (ha : ∀ i, a i ≠ 0 → (typeDRootPairing_base 2).IsPos (w.val (rootIndex i))) :
    D.lift w * orderedProduct _ a * (D.lift w)⁻¹ ∈ positiveSubgroup _ := by
  apply conjugate_list_prod_mem
  intro g hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
  by_cases hi : a i = 0
  · simp [hi]
  · change D.lift w * rootCurve _ (rootIndex i) (a i) * (D.lift w)⁻¹ ∈ _
    rw [lift_conjugate_root]
    have hr : w.val (rootIndex i) ∈ Set.range rootIndex := by
      rw [range_rootIndex]
      exact ha i hi
    obtain ⟨j, hj⟩ := hr
    rw [← hj, rootCurve_positive]
    exact curve_mem_positiveSubgroup_of_sumExchange _ (sumExchange_binary n hn) j (a i)

end
end Triality.Standard.ConcreteBruhat.SplitNormalForm.CellCollection
