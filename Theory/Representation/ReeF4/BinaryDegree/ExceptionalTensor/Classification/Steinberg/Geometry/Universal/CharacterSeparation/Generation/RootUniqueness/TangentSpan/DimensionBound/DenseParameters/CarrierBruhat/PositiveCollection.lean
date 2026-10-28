module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentSpan.DimensionBound.DenseParameters.CarrierBruhat.PositiveCollection.Ordering
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentSpan.DimensionBound.DenseParameters.CarrierBruhat.PositiveCollection.Exchanges

/-!
# Positive-root collection in the literal F4 carrier

Closure induction writes each positive-unipotent element as a word in the
actual root curves, absorbing inverses by negating parameters. Height-filtered
Chevalley exchanges then collect the word in any prescribed root order.
Ordering all roots assigned to one subgroup before the remaining roots proves
the root-partition factorization as well.

This uses `Theory.GroupTheory.FilteredCollection`, the generic extraction of
the collection algorithm in `G2ChevalleyBorelWeylExchange`. The word and
partition proofs adapt `SplitCoordinates.Collection` and the local-block
`FixedBruhatCover.SplitCoverage.Collection` to the algebraic carrier.
Source: GLS3 1.11–1.12, especially 1.12.1(a,b),
`refs/KGroup/GLS3/Chapter1.tex`. No global Bruhat cover or uniqueness is assumed.
-/

public section
noncomputable section
namespace Theory.AlgebraicGroup.F4Chevalley.DenseParameters.CarrierBruhat
open StandardRootSystem FilteredCollection CollectionMatrices

variable {k : Type*} [Field k] [IsAlgClosed k]

private theorem positiveUnipotent_eq_closure :
    positiveUnipotent (k := k) = Subgroup.closure
      {x | ∃ (r : PositiveRoot) (t : k), x = rootElement r.val t} := by
  apply congrArg Subgroup.closure
  ext x
  constructor
  · rintro ⟨r, t, hr, rfl⟩
    exact ⟨⟨r, hr⟩, t, rfl⟩
  · rintro ⟨r, t, rfl⟩
    exact ⟨r.val, t, r.property, rfl⟩

private theorem rootWord_inv (w : List (PositiveRoot × k)) :
    (wordProduct (fun r : PositiveRoot => rootElement r.val) w)⁻¹ =
      wordProduct (fun r : PositiveRoot => rootElement r.val)
        (w.reverse.map (fun z => (z.1, -z.2))) := by
  induction w with
  | nil => simp [wordProduct]
  | cons z w ih =>
      simpa only [wordProduct, List.map_cons, List.prod_cons,
        List.reverse_cons, List.map_append, List.map_map, List.prod_append,
        List.map_nil, List.prod_nil, mul_one, Function.comp_def,
        mul_inv_rev, rootElement_inv] using congrArg
          (fun y => y * rootElement z.1.val (-z.2)) ih

/-- Elements of the generated positive subgroup are literal finite root words. -/
theorem exists_positiveRootWord (u : Variety.Point (Carrier (k := k)))
    (hu : u ∈ positiveUnipotent (k := k)) :
    ∃ w : List (PositiveRoot × k),
      u = wordProduct (fun r : PositiveRoot => rootElement r.val) w := by
  rw [positiveUnipotent_eq_closure] at hu
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨r, t, rfl⟩ := hx
      exact ⟨[(r, t)], by simp [wordProduct]⟩
  | one => exact ⟨[], by simp [wordProduct]⟩
  | mul x y _ _ hx hy =>
      obtain ⟨w, rfl⟩ := hx
      obtain ⟨v, rfl⟩ := hy
      exact ⟨w ++ v, by simp [wordProduct]⟩
  | inv x _ hx =>
      obtain ⟨w, rfl⟩ := hx
      exact ⟨w.reverse.map (fun z => (z.1, -z.2)), rootWord_inv w⟩

variable [CharP k 2]

private theorem collect_positiveRootWord (order : List PositiveRoot)
    (hnd : order.Nodup) (hmem : ∀ r, r ∈ order) (w : List (PositiveRoot × k)) :
    ∃ t : PositiveRoot → k,
      wordProduct (fun r : PositiveRoot => rootElement r.val) w =
        (order.map fun r => rootElement r.val (t r)).prod := by
  classical
  let : Fintype PositiveRoot := Fintype.ofFinite _
  exact filteredCollection_exists_params
    (fun r : PositiveRoot => rootDegree r.val)
    (fun r : PositiveRoot => rootElement r.val) order hnd
    ((Finset.univ.sup fun r : PositiveRoot => rootDegree r.val) + 1)
    (fun r _ => Nat.lt_succ_of_le (Finset.le_sup (f := fun r : PositiveRoot =>
      rootDegree r.val) (Finset.mem_univ r)))
    (fun r a b => (rootElement_add r.val a b).symm)
    (fun r s a b _ _ hne => by
      obtain ⟨c, hc, he⟩ := positiveRoot_exchange r s a b hne
      exact ⟨c, fun z hz => ⟨hmem z.1, hc z hz⟩, he⟩)
    w (fun z _ => hmem z.1)

/-- Every positive-unipotent element has coordinates in every positive root ordering. -/
theorem orderedPositiveCoverage : OrderedPositiveCoverage (k := k) := by
  intro p u hu
  obtain ⟨w, hw⟩ := exists_positiveRootWord u hu
  obtain ⟨t, ht⟩ := collect_positiveRootWord (List.ofFn p)
    (List.nodup_ofFn.mpr p.injective)
    (fun r => List.mem_ofFn.mpr (p.surjective r)) w
  refine ⟨fun i => t (p i), ?_⟩
  rw [hw, ht]
  simp only [rootProduct, List.map_ofFn, Function.comp_def]

/-- Roots assigned to one subgroup can all be collected before those assigned
to the other, giving the exact root-partition contract from `Basic`. -/
theorem positiveRootPartition : PositiveRootPartition (k := k) := by
  classical
  intro A B hroot u hu
  let : Fintype PositiveRoot := Fintype.ofFinite _
  let roots := (Finset.univ : Finset PositiveRoot).toList
  let p : PositiveRoot → Prop := fun r => ∀ t : k, rootElement r.val t ∈ A
  let left := roots.filter (fun r => decide (p r))
  let right := roots.filter (fun r => decide (¬ p r))
  let order := left ++ right
  have hmem (r : PositiveRoot) : r ∈ order := by
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
    have hp : p a := of_decide_eq_true (List.mem_filter.mp ha).2
    have hn : ¬ p a := of_decide_eq_true (List.mem_filter.mp hb).2
    exact hn hp
  obtain ⟨w, hw⟩ := exists_positiveRootWord u hu
  obtain ⟨t, ht⟩ := collect_positiveRootWord order hnd hmem w
  refine ⟨(left.map fun r => rootElement r.val (t r)).prod, ?_,
    (right.map fun r => rootElement r.val (t r)).prod, ?_, ?_⟩
  · apply A.list_prod_mem
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    have hp : p r := of_decide_eq_true (List.mem_filter.mp hr).2
    exact hp (t r)
  · apply B.list_prod_mem
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    have hn : ¬ p r := of_decide_eq_true (List.mem_filter.mp hr).2
    exact ((hroot r).resolve_left hn) (t r)
  · rw [hw, ht]
    simp only [order, List.map_append, List.prod_append]

end Theory.AlgebraicGroup.F4Chevalley.DenseParameters.CarrierBruhat
