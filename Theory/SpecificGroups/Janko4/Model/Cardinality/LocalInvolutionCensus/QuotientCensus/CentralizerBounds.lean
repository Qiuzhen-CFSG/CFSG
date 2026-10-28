module
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.QuotientCensus.FiniteData

/-!
# Lower bounds for the three marked quotient centralizers

The finite tables select elements of the actual twelve-dimensional quotient
image Q. For each marked image q(lift j), we check both products with each
selected generator, then check a multiplication tree rooted at the identity.
Thus every table entry lies in its centralizer. Adjacent sorted matrix codes
are strictly increasing, so the sorted table injects into that centralizer.
This yields the lower bounds 640, 2688 and 2304 without an exhaustive
centralizer computation or any additional group-order hypothesis.

The numeric checks use kernel reduction and transfer through the checked
program's matrix realization. The sorting map needs no permutation property:
its composite with the table already supplies the required injection.

These bounds support the local class census used in the order estimates of
Aschbacher--Smith, `refs/quasithin.pdf`, printed pp.64--65, A.6.1--4. Witness
conventions are in `QuotientCensus/source/README.md`; the underlying ATLAS
matrix provenance remains in `TwoCoreCentralizer/source/`.
-/

set_option maxRecDepth 100000

namespace Janko4.Cardinality.LocalInvolutionCensus.QuotientCensus

/-- Transfer checked finite data to an injection into the actual centralizer. -/
private theorem card_ge_of_checked_tree {n k : ℕ} (j : Fin 4)
    (genIndex : Fin k → Fin 7392) (tableIndex : Fin (n + 1) → Fin 7392)
    (parent : Fin (n + 1) → Fin (n + 1)) (letter : Fin (n + 1) → Fin k)
    (sorted : Fin (n + 1) → Fin (n + 1)) (commProductIndex : Fin k → Fin 7392)
    (hroot : tableIndex 0 = 0)
    (hcomm : ∀ a, productCheck (genIndex a) (markedIndex j) (commProductIndex a) ∧
      productCheck (markedIndex j) (genIndex a) (commProductIndex a))
    (htree : ∀ i, i ≠ 0 → parent i < i ∧
      productCheck (tableIndex (parent i)) (genIndex (letter i)) (tableIndex i))
    (hsorted : ∀ i : Fin n, (code (tableIndex (sorted i.castSucc))).toNat <
      (code (tableIndex (sorted i.succ))).toNat) :
    n + 1 ≤ Nat.card (Subgroup.centralizer {q (lift j)}) := by
  have hgen (a : Fin k) : element (genIndex a) ∈ Subgroup.centralizer {q (lift j)} := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← element_marked j]
    exact (productCheck_sound (hcomm a).1).trans (productCheck_sound (hcomm a).2).symm
  have hmem : ∀ i, element (tableIndex i) ∈ Subgroup.centralizer {q (lift j)} :=
    tree_mem _ (fun a => element (genIndex a)) (fun i => element (tableIndex i))
      parent letter hgen (by rw [hroot, element_zero])
      (fun i hi => (htree i hi).1) (fun i hi => productCheck_sound (htree i hi).2)
  have hinj : Function.Injective (fun i => element (tableIndex (sorted i))) :=
    table_injective _ (fun i => code (tableIndex (sorted i)))
      (fun i => element_val _) hsorted
  let f : Fin (n + 1) → Subgroup.centralizer {q (lift j)} :=
    fun i => ⟨element (tableIndex (sorted i)), hmem (sorted i)⟩
  have hf : Function.Injective f := fun _ _ h => hinj (congrArg Subtype.val h)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

namespace Centralizer640

private theorem generators_checked : ∀ a,
    productCheck (genIndex a) (markedIndex 1) (commProductIndex a) ∧
    productCheck (markedIndex 1) (genIndex a) (commProductIndex a) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem tree_checked : ∀ i, i ≠ 0 → parent i < i ∧
    productCheck (tableIndex (parent i)) (genIndex (letter i)) (tableIndex i) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem sorted_checked : ∀ i : Fin 639,
    (code (tableIndex (sorted i.castSucc))).toNat <
      (code (tableIndex (sorted i.succ))).toNat := by
  apply forall_fin_of_range
  decide +kernel

end Centralizer640

/-- The centralizer of the marked image `q (lift 1)` has at least 640 elements. -/
public theorem centralizer640_card_ge : 640 ≤ Nat.card (Subgroup.centralizer {q (lift 1)}) := by
  exact card_ge_of_checked_tree 1 Centralizer640.genIndex Centralizer640.tableIndex
    Centralizer640.parent Centralizer640.letter Centralizer640.sorted
    Centralizer640.commProductIndex (by decide +kernel) Centralizer640.generators_checked
    Centralizer640.tree_checked Centralizer640.sorted_checked

namespace Centralizer2688

private theorem generators_checked : ∀ a,
    productCheck (genIndex a) (markedIndex 2) (commProductIndex a) ∧
    productCheck (markedIndex 2) (genIndex a) (commProductIndex a) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem tree_checked : ∀ i, i ≠ 0 → parent i < i ∧
    productCheck (tableIndex (parent i)) (genIndex (letter i)) (tableIndex i) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem sorted_checked : ∀ i : Fin 2687,
    (code (tableIndex (sorted i.castSucc))).toNat <
      (code (tableIndex (sorted i.succ))).toNat := by
  apply forall_fin_of_range
  decide +kernel

end Centralizer2688

/-- The centralizer of the marked image `q (lift 2)` has at least 2688 elements. -/
public theorem centralizer2688_card_ge : 2688 ≤ Nat.card (Subgroup.centralizer {q (lift 2)}) := by
  exact card_ge_of_checked_tree 2 Centralizer2688.genIndex Centralizer2688.tableIndex
    Centralizer2688.parent Centralizer2688.letter Centralizer2688.sorted
    Centralizer2688.commProductIndex (by decide +kernel) Centralizer2688.generators_checked
    Centralizer2688.tree_checked Centralizer2688.sorted_checked

namespace Centralizer2304

private theorem generators_checked : ∀ a,
    productCheck (genIndex a) (markedIndex 3) (commProductIndex a) ∧
    productCheck (markedIndex 3) (genIndex a) (commProductIndex a) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem tree_checked : ∀ i, i ≠ 0 → parent i < i ∧
    productCheck (tableIndex (parent i)) (genIndex (letter i)) (tableIndex i) := by
  apply forall_fin_of_range
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem sorted_checked : ∀ i : Fin 2303,
    (code (tableIndex (sorted i.castSucc))).toNat <
      (code (tableIndex (sorted i.succ))).toNat := by
  apply forall_fin_of_range
  decide +kernel

end Centralizer2304

/-- The centralizer of the marked image `q (lift 3)` has at least 2304 elements. -/
public theorem centralizer2304_card_ge : 2304 ≤ Nat.card (Subgroup.centralizer {q (lift 3)}) := by
  exact card_ge_of_checked_tree 3 Centralizer2304.genIndex Centralizer2304.tableIndex
    Centralizer2304.parent Centralizer2304.letter Centralizer2304.sorted
    Centralizer2304.commProductIndex (by decide +kernel) Centralizer2304.generators_checked
    Centralizer2304.tree_checked Centralizer2304.sorted_checked

end Janko4.Cardinality.LocalInvolutionCensus.QuotientCensus
