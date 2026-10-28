module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Splitting.Inputs
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Normalization.Basic
public import Theory.GroupTheory.FilteredCollection
public import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

/-!
# Collection across actual D4 root partitions

Pairwise root-subgroup commutator containment gives an exchange of two root
parameters with a correction word supported on roots of strictly greater
height. The finite filtered collector then collects every generated positive
word into any chosen duplicate-free root order. Choosing retained roots first
and inverted roots second proves the ordered two-factor product needed for
Bruhat splitting.

The given one-parameter isomorphisms are used directly. No Chevalley
coefficient normalization, matrix-model comparison, or normalizer realization
is assumed. The `PositiveCoordinates` witness supplies a finite root
enumeration; its single-order coverage is not used as arbitrary-order
coverage. Pairwise commutator containment remains an explicit geometric
premise, to be discharged by its separate construction from `Geometry`.

Sources: GLS3 Theorem 1.12.7(a)--(c),
`refs/KGroup/GLS3/Chapter1.tex`, and Steinberg 6.2(b),
`refs/KGroup/GLS3/Chapter2St2.tex`.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped BigOperators commutatorElement

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
namespace ConnectedCentralizer.Bruhat.Splitting
noncomputable section
universe u
variable {k : Type u} [Field k] [CharP k 2]
  {K : Variety k} [AlgebraicGroup K]

open Coordinates.Normalization

private def rootElement (S : Geometry K) (a : S.roots.Root) (t : k) : Variety.Point K :=
  (S.roots.rootSubgroup a).includePoint ((S.rootParameter a).value t)

private def parameterEquiv (S : Geometry K) (a : S.roots.Root) :
    k ≃ (S.roots.rootSubgroup a).toSubgroup :=
  (Multiplicative.ofAdd.trans (additiveGroupPointEquiv k).symm).trans
    ((S.rootParameter a).toMulEquiv.toEquiv.trans (S.roots.rootSubgroup a).pointEquiv)

private lemma rootElement_mem (S : Geometry K) (a : S.roots.Root) (t : k) :
    rootElement S a t ∈ (S.roots.rootSubgroup a).toSubgroup :=
  (parameterEquiv S a t).property

private lemma rootElement_add (S : Geometry K) (a : S.roots.Root) (t s : k) :
    rootElement S a t * rootElement S a s = rootElement S a (t + s) := by
  change (S.roots.rootSubgroup a).inclusion.onPoints
      ((S.rootParameter a).hom.onPoints (kPlusPoint t)) *
    (S.roots.rootSubgroup a).inclusion.onPoints
      ((S.rootParameter a).hom.onPoints (kPlusPoint s)) = _
  rw [← map_mul, ← map_mul, kPlusPoint_mul]
  rfl

private lemma rootElement_zero (S : Geometry K) (a : S.roots.Root) :
    rootElement S a 0 = 1 := by
  simpa using rootElement_add S a 0 0

private lemma rootElement_neg (S : Geometry K) (a : S.roots.Root) (t : k) :
    rootElement S a (-t) = (rootElement S a t)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  rw [rootElement_add, neg_add_cancel, rootElement_zero]

private theorem generated_exists_word (S : Geometry K) (A : Set S.roots.Root)
    (x : Variety.Point K) (hx : x ∈ RootSubgroupGenerated S.roots A) :
    ∃ word : List (S.roots.Root × k),
      (∀ z ∈ word, z.1 ∈ A) ∧ x = FilteredCollection.wordProduct (rootElement S) word := by
  classical
  have hinv : ∀ word : List (S.roots.Root × k),
      (FilteredCollection.wordProduct (rootElement S) word)⁻¹ =
        FilteredCollection.wordProduct (rootElement S)
          (word.reverse.map fun z => (z.1, -z.2)) := by
    intro word
    induction word with
    | nil => simp [FilteredCollection.wordProduct]
    | cons z tail ih =>
      simp only [FilteredCollection.wordProduct, List.map_cons, List.prod_cons,
        List.reverse_cons, List.map_append, List.map_map, List.prod_append,
        mul_inv_rev] at ih ⊢
      rw [ih, rootElement_neg]
      simp
  refine Subgroup.closure_induction
    (p := fun x _ => ∃ word : List (S.roots.Root × k),
      (∀ z ∈ word, z.1 ∈ A) ∧ x = FilteredCollection.wordProduct (rootElement S) word)
    ?_ ?_ ?_ ?_ hx
  · intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨t, ht⟩ := (parameterEquiv S a).surjective ⟨x, hxa⟩
    refine ⟨[(a, t)], by simpa using ha, ?_⟩
    have ht' : rootElement S a t = x := by
      change ((parameterEquiv S a) t).val = x
      exact congrArg Subtype.val ht
    simpa only [FilteredCollection.wordProduct, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one] using ht'.symm
  · exact ⟨[], by simp, by simp [FilteredCollection.wordProduct]⟩
  · intro x y _ _
    rintro ⟨wx, hwx, rfl⟩ ⟨wy, hwy, rfl⟩
    refine ⟨wx ++ wy, ?_, by simp [FilteredCollection.wordProduct]⟩
    intro z hz
    exact (List.mem_append.mp hz).elim (hwx z) (hwy z)
  · intro x _
    rintro ⟨word, hword, rfl⟩
    refine ⟨word.reverse.map fun z => (z.1, -z.2), ?_, hinv word⟩
    intro z hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    exact hword y (List.mem_reverse.mp hy)

private def rootHeight (S : Geometry K) (a : S.roots.Root) : ℤ :=
  (typeDRootPairing_base 2).height (S.rootIndex a)

private lemma rootHeight_combination (S : Geometry K) {a b c : S.roots.Root} {i j : ℕ}
    (hroot : (typeDRootPairing 2).root (S.rootIndex c) =
      (i : ℝ) • (typeDRootPairing 2).root (S.rootIndex a) +
      (j : ℝ) • (typeDRootPairing 2).root (S.rootIndex b)) :
    rootHeight S c = (i : ℤ) * rootHeight S a + (j : ℤ) * rootHeight S b := by
  classical
  let P := typeDRootPairing 2
  let base := typeDRootPairing_base 2
  obtain ⟨f, -, -, hf⟩ := base.exists_root_eq_sum_int (S.rootIndex a)
  obtain ⟨g, -, -, hg⟩ := base.exists_root_eq_sum_int (S.rootIndex b)
  have hf : P.root (S.rootIndex a) = ∑ l ∈ base.support, f l • P.root l := hf
  have hg : P.root (S.rootIndex b) = ∑ l ∈ base.support, g l • P.root l := hg
  have hc : P.root (S.rootIndex c) =
      ∑ l ∈ base.support, ((i : ℤ) * f l + (j : ℤ) * g l) • P.root l := by
    have hroot' : P.root (S.rootIndex c) = (i : ℤ) • P.root (S.rootIndex a) +
        (j : ℤ) • P.root (S.rootIndex b) := by
      simpa only [Nat.cast_smul_eq_nsmul ℝ, ← natCast_zsmul] using hroot
    rw [hroot', hf, hg]
    simp_rw [Finset.smul_sum, smul_smul, add_zsmul, Finset.sum_add_distrib]
  change base.height _ = (i : ℤ) * base.height _ + (j : ℤ) * base.height _
  rw [base.height_eq_sum hc, base.height_eq_sum hf, base.height_eq_sum hg]
  simp_rw [Finset.sum_add_distrib, Finset.mul_sum]

private lemma correction_degree_gt (S : Geometry K) {a b c : S.roots.Root}
    (ha : a ∈ S.roots.positive) (hb : b ∈ S.roots.positive)
    (hc : c ∈ positiveCommutatorRoots S a b) :
    max (rootHeight S a).toNat (rootHeight S b).toNat < (rootHeight S c).toNat := by
  obtain ⟨_, i, j, hi, hj, hroot⟩ := hc
  have ha' : 0 < rootHeight S a := by
    simpa only [RootPairing.Base.isPos_iff, rootHeight] using (S.positive a).mp ha
  have hb' : 0 < rootHeight S b := by
    simpa only [RootPairing.Base.isPos_iff, rootHeight] using (S.positive b).mp hb
  have hi' : (1 : ℤ) ≤ i := by exact_mod_cast hi
  have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
  rw [rootHeight_combination S hroot]
  apply max_lt
  · exact (Int.toNat_lt_toNat (by nlinarith)).mpr (by nlinarith)
  · exact (Int.toNat_lt_toNat (by nlinarith)).mpr (by nlinarith)

private theorem exchange_exists_word (S : Geometry K)
    (hcomm : PositiveCommutatorContainment S)
    {a b : S.roots.Root} (ha : a ∈ S.roots.positive) (hb : b ∈ S.roots.positive)
    (hne : a ≠ b) (t s : k) :
    ∃ word : List (S.roots.Root × k),
      (∀ z ∈ word, z.1 ∈ S.roots.positive ∧
        max (rootHeight S a).toNat (rootHeight S b).toNat < (rootHeight S z.1).toNat) ∧
      rootElement S a t * rootElement S b s =
        rootElement S b s * rootElement S a t *
          FilteredCollection.wordProduct (rootElement S) word := by
  have hx := (S.roots.rootSubgroup a).toSubgroup.inv_mem (rootElement_mem S a t)
  have hy := (S.roots.rootSubgroup b).toSubgroup.inv_mem (rootElement_mem S b s)
  have hc := hcomm a ha b hb hne (Subgroup.commutator_mem_commutator hx hy)
  obtain ⟨word, hword, heq⟩ := generated_exists_word S _ _ hc
  refine ⟨word, ?_, ?_⟩
  · intro z hz
    exact ⟨(hword z hz).1, correction_degree_gt S ha hb (hword z hz)⟩
  · rw [← heq]
    simp only [commutatorElement_def, inv_inv]
    group

/-- Pairwise actual root commutator containment collects every positive-root
word in any prescribed duplicate-free order. Only containment is required;
the given root parameters need no Chevalley coefficient normalization. -/
public theorem positiveRootProduct_exists_of_positiveCommutatorContainment
    (S : Geometry K) (hcomm : PositiveCommutatorContainment S)
    (order : List S.roots.Root) (hnd : order.Nodup)
    (hmem : ∀ a, a ∈ order ↔ a ∈ S.roots.positive)
    (x : Variety.Point K) (hx : x ∈ positiveGroup S) :
    ∃ params : S.roots.Root → k,
      x = (order.map fun a => (S.roots.rootSubgroup a).includePoint
        ((S.rootParameter a).value (params a))).prod := by
  classical
  let degree : S.roots.Root → ℕ := fun a => (rootHeight S a).toNat
  let bound := (order.map degree).sum + 1
  have hbound : ∀ a ∈ order, degree a < bound := by
    intro a ha
    exact (List.le_sum_of_mem (List.mem_map_of_mem ha)).trans_lt (Nat.lt_succ_self _)
  have hswap : ∀ a b t s, a ∈ order → b ∈ order → a ≠ b →
      ∃ word : List (S.roots.Root × k),
        (∀ z ∈ word, z.1 ∈ order ∧ max (degree a) (degree b) < degree z.1) ∧
        rootElement S a t * rootElement S b s =
          rootElement S b s * rootElement S a t *
            FilteredCollection.wordProduct (rootElement S) word := by
    intro a b t s ha hb hne
    obtain ⟨word, hword, heq⟩ := exchange_exists_word S hcomm
      ((hmem a).mp ha) ((hmem b).mp hb) hne t s
    exact ⟨word, fun z hz => ⟨(hmem z.1).mpr (hword z hz).1, (hword z hz).2⟩, heq⟩
  obtain ⟨word, hword, rfl⟩ := generated_exists_word S _ x hx
  exact FilteredCollection.filteredCollection_exists_params degree (rootElement S)
    order hnd bound hbound (rootElement_add S) hswap word
    (fun z hz => (hmem z.1).mpr (hword z hz))

/-- Actual positive-root commutator containment gives the ordered two-factor
product for every Weyl inversion partition. The coordinate witness supplies
a finite enumeration only; arbitrary-order collection is proved above. -/
public theorem rootPartitionProducts_of_positiveCommutatorContainment
    (S : Geometry K) (C : PositiveCoordinates S)
    (hcomm : PositiveCommutatorContainment S) : RootPartitionProducts S := by
  classical
  intro w q hq
  let p : S.roots.Root → Bool := fun a => decide (rootAction S w a ∈ S.roots.positive)
  let left := C.roots.filter p
  let right := C.roots.filter (fun a => !p a)
  have hleft : ∀ a, a ∈ left ↔ a ∈ retainedRoots S w := by
    intro a
    simp only [left, List.mem_filter, p, decide_eq_true_eq, C.mem_roots, retainedRoots,
      Set.mem_ofPred_eq]
  have hright : ∀ a, a ∈ right ↔ a ∈ inversionRoots S w := by
    intro a
    simp [right, p, C.mem_roots, inversionRoots]
  have hnd : (left ++ right).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨C.nodup.filter p, C.nodup.filter (fun a => !p a), ?_⟩
    rw [List.disjoint_left]
    intro a ha hb
    exact ((hright a).mp hb).2 ((hleft a).mp ha).2
  have hmem : ∀ a, a ∈ left ++ right ↔ a ∈ S.roots.positive := by
    intro a
    rw [List.mem_append, hleft, hright]
    change (_ ∧ _) ∨ (_ ∧ ¬ _) ↔ _
    tauto
  obtain ⟨params, hparams⟩ :=
    positiveRootProduct_exists_of_positiveCommutatorContainment S hcomm
      (left ++ right) hnd hmem q hq
  let f : S.roots.Root → Variety.Point K := fun a =>
    (S.roots.rootSubgroup a).includePoint ((S.rootParameter a).value (params a))
  refine ⟨(left.map f).prod, (right.map f).prod, ?_, ?_, ?_⟩
  · apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact rootSubgroup_le_RootSubgroupGenerated S.roots ((hleft a).mp ha)
      (rootElement_mem S a (params a))
  · apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact rootSubgroup_le_RootSubgroupGenerated S.roots ((hright a).mp ha)
      (rootElement_mem S a (params a))
  · simpa only [List.map_append, List.prod_append] using hparams

end
end ConnectedCentralizer.Bruhat.Splitting
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
