module

public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection.Relations
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection.NonsumCommute
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection.SumExchange
public import Theory.GroupTheory.FilteredCollection

/-!
# Collection and positive generation for the binary D4 curves

Assume the two explicit identities `SumExchange` and `NonsumCommute` on the
actual integral Geck curves. Root height makes their correction terms strictly
higher, so the finite filtered collector rewrites every positive word as the
published twelve-root ordered product. The eight parent decompositions in
`Roots` express every nonsimple positive curve as a commutator of earlier
positive curves. Thus all twelve curves lie in the existing subgroup generated
by the four positive simple curves, and the ordered product has exactly that
subgroup as its image.

The general reduction keeps the matrix identities as explicit hypotheses.
The final theorem `range_orderedProduct_binary` discharges both with the proved
canonical matrix identities, for every positive binary exponent, including one.
No injectivity, graph-field equivariance, or normal-form hypothesis is used.

Source: GLS3, 2.3.6–7 and §§2.4–2.6
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section

open Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.Standard.PositiveCoordinates

/-- The eight nonsimple positive curves are generated recursively by the four
positive simple curves, using only root-sum exchanges. -/
theorem curve_mem_positiveSubgroup_of_sumExchange (P : Parameters) (hsum : SumExchange P)
    (i : Fin 12) (t : ExtensionField P) : curve P i t ∈ Parabolics.positiveSubgroup P := by
  have hs (j : Fin 4) (s : ExtensionField P) :
      curve P (simplePosition j) s ∈ Parabolics.positiveSubgroup P := by
    rw [curve_simple]
    exact Subgroup.subset_closure ⟨j, s, rfl⟩
  have hadd (j : Fin 8)
      (hl : ∀ s, curve P (leftParent j) s ∈ Parabolics.positiveSubgroup P)
      (hr : ∀ s, curve P (rightParent j) s ∈ Parabolics.positiveSubgroup P)
      (s : ExtensionField P) :
      curve P ⟨j + 4, by omega⟩ s ∈ Parabolics.positiveSubgroup P := by
    have hx := hsum (leftParent j) (rightParent j) ⟨j + 4, by omega⟩ (root_add j) s 1
    simp only [mul_one] at hx
    have heq : curve P ⟨j + 4, by omega⟩ s =
        (curve P (rightParent j) 1 * curve P (leftParent j) s)⁻¹ *
          (curve P (leftParent j) s * curve P (rightParent j) 1) := by
      rw [hx, inv_mul_cancel_left]
    rw [heq]
    exact Subgroup.mul_mem _
      (Subgroup.inv_mem _ (Subgroup.mul_mem _ (hr 1) (hl s)))
      (Subgroup.mul_mem _ (hl s) (hr 1))
  have h0 := hs 0
  have h1 := hs 2
  have h2 := hs 3
  have h3 := hs 1
  have h4 := hadd 0 h0 h3
  have h5 := hadd 1 h1 h3
  have h6 := hadd 2 h2 h3
  have h7 := hadd 3 h4 h1
  have h8 := hadd 4 h5 h2
  have h9 := hadd 5 h6 h0
  have h10 := hadd 6 h7 h2
  have h11 := hadd 7 h10 h3
  fin_cases i
  · exact h0 t
  · exact h1 t
  · exact h2 t
  · exact h3 t
  · exact h4 t
  · exact h5 t
  · exact h6 t
  · exact h7 t
  · exact h8 t
  · exact h9 t
  · exact h10 t
  · exact h11 t

open FilteredCollection in
/-- Collect an arbitrary word in the actual positive curves. Every exchange
emits either no correction or one factor of strictly larger root height. -/
theorem positive_word_collected_of_relations (P : Parameters)
    (hsum : SumExchange P) (hcomm : NonsumCommute P)
    (word : List (Fin 12 × ExtensionField P)) :
    ∃ a : Coordinates P, wordProduct (curve P) word = orderedProduct P a := by
  classical
  have hswap : ∀ (i j : Fin 12) (a b : ExtensionField P),
      i ∈ List.finRange 12 → j ∈ List.finRange 12 → i ≠ j →
      ∃ correction : List (Fin 12 × ExtensionField P),
        (∀ z ∈ correction, z.1 ∈ List.finRange 12 ∧
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
        exact ⟨List.mem_finRange k, collectionHeight_sum_gt hk⟩
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one] using hsum i j k hk a b
    · refine ⟨[], by simp, ?_⟩
      simpa only [wordProduct, List.map_nil, List.prod_nil, mul_one] using (hcomm i j hij h a b).eq
  obtain ⟨a, ha⟩ := filteredCollection_exists_params collectionHeight (curve P)
    (List.finRange 12) (List.nodup_finRange 12) 6
    (fun i _ => collectionHeight_lt_six i)
    (fun i a b => (curve_add P i a b).symm) hswap word
    (fun z _ => List.mem_finRange z.1)
  exact ⟨a, by simpa only [orderedProduct, List.ofFn_eq_map] using ha⟩

open FilteredCollection in
private lemma positive_word_inv (P : Parameters) (word : List (Fin 12 × ExtensionField P)) :
    wordProduct (curve P) ((word.map fun z => (z.1, -z.2)).reverse) =
      (wordProduct (curve P) word)⁻¹ := by
  simp only [wordProduct, List.map_reverse, List.map_map, List.prod_inv_reverse]
  apply congrArg List.prod
  apply congrArg List.reverse
  apply List.map_congr_left
  intro z _
  exact (curve_inv P z.1 z.2).symm

open FilteredCollection in
/-- An element of the subgroup generated by positive simple curves is a word
in the twelve positive curves. This direction needs no exchange identity. -/
theorem exists_positive_word_of_mem_positiveSubgroup (P : Parameters) {g : SplitGroup P}
    (hg : g ∈ Parabolics.positiveSubgroup P) :
    ∃ word : List (Fin 12 × ExtensionField P), wordProduct (curve P) word = g := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, t, rfl⟩ := hg
    exact ⟨[(simplePosition i, t)], by simp [wordProduct]⟩
  | one => exact ⟨[], by simp [wordProduct]⟩
  | mul g h _ _ hg hh =>
    obtain ⟨v, rfl⟩ := hg
    obtain ⟨w, rfl⟩ := hh
    exact ⟨v ++ w, by simp [wordProduct]⟩
  | inv g _ hg =>
    obtain ⟨word, rfl⟩ := hg
    exact ⟨(word.map fun z => (z.1, -z.2)).reverse, positive_word_inv P word⟩

/-- Positive generation gives the first inclusion of the normal-form image. -/
theorem orderedProduct_mem_positiveSubgroup_of_sumExchange (P : Parameters)
    (hsum : SumExchange P) (a : Coordinates P) :
    orderedProduct P a ∈ Parabolics.positiveSubgroup P := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
  exact curve_mem_positiveSubgroup_of_sumExchange P hsum i (a i)

/-- The two local matrix identities suffice for the exact image identity. -/
theorem range_orderedProduct_of_relations (P : Parameters)
    (hsum : SumExchange P) (hcomm : NonsumCommute P) :
    Set.range (orderedProduct P) = (Parabolics.positiveSubgroup P : Set (SplitGroup P)) := by
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    exact orderedProduct_mem_positiveSubgroup_of_sumExchange P hsum a
  · intro hg
    obtain ⟨word, rfl⟩ := exists_positive_word_of_mem_positiveSubgroup P hg
    obtain ⟨a, ha⟩ := positive_word_collected_of_relations P hsum hcomm word
    exact ⟨a, ha.symm⟩

/-- The twelve-root ordered product has image exactly the subgroup generated
by the four positive simple curves, for every positive binary exponent. -/
theorem range_orderedProduct_binary (n : ℕ) (hn : 0 < n) :
    Set.range (orderedProduct (binaryParameters n hn)) =
      (Parabolics.positiveSubgroup (binaryParameters n hn) :
        Set (SplitGroup (binaryParameters n hn))) :=
  range_orderedProduct_of_relations (binaryParameters n hn)
    (sumExchange_binary n hn) (nonsumCommute_binary n hn)

end Triality.Standard.PositiveCoordinates
