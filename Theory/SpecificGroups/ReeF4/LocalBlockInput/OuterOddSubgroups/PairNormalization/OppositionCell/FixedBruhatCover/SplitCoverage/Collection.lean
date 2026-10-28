module
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.SplitCoverage.RootConditions

/-!
# Positive-root collection across a partition

Filtered root exchanges allow the factors assigned to one subgroup to precede
all factors assigned to another. This is the collection step of GLS3 1.11.5
(`refs/KGroup/GLS3/Chapter1.tex`), without an assumption of global coverage. The argument works over every
coefficient field. It extends the partition-collection argument in the binary
split Bruhat development, preserving its original module.
-/

public section
noncomputable section
namespace ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Parabolics.RadicalCoordinates LargeLocalSeeds Subgroup FilteredCollection

/-- Filtered collection orders the roots assigned to `A` before those assigned to `B`. -/
theorem positive_factorization_of_root_partition (m : ℕ)
    (hswap : PositiveRootExchanges m) (A B : Subgroup (SplitGroup m))
    (hroot : ∀ r : Root .positive,
      (∀ t, rootGeneratorInGroup m r.val t ∈ A) ∨
      (∀ t, rootGeneratorInGroup m r.val t ∈ B))
    {u : SplitGroup m} (hu : u ∈ splitUnipotent m) :
    ∃ a ∈ A, ∃ b ∈ B, u = a * b := by
  classical
  let : Fintype (Root .positive) := Fintype.ofFinite _
  let roots := (Finset.univ : Finset (Root .positive)).toList
  let p : Root .positive → Prop := fun r => ∀ t, rootGeneratorInGroup m r.val t ∈ A
  let left := roots.filter (fun r => decide (p r))
  let right := roots.filter (fun r => decide (¬ p r))
  let order := left ++ right
  have hmem (r : Root .positive) : r ∈ order := by
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
  obtain ⟨w, hw⟩ := exists_rootWord m (k := .positive) u hu
  obtain ⟨t, ht⟩ := filteredCollection_exists_params
    (fun r : Root .positive => rootDegree r.val)
    (fun r : Root .positive => rootGeneratorInGroup m r.val) order hnd
    ((Finset.univ.sup fun r : Root .positive => rootDegree r.val) + 1)
    (fun r _ => Nat.lt_succ_of_le (Finset.le_sup (f := fun r : Root .positive =>
      rootDegree r.val) (Finset.mem_univ r)))
    (fun r a b => by apply Subtype.ext; exact (F4Chevalley.rootCurve_add r.val a b).symm)
    (fun r s a b _ _ hne => by
      obtain ⟨c, hc, he⟩ := hswap r s a b hne
      exact ⟨c, fun z hz => ⟨hmem z.1, hc z hz⟩, he⟩)
    w (fun z _ => hmem z.1)
  refine ⟨(left.map fun r => rootGeneratorInGroup m r.val (t r)).prod, ?_,
    (right.map fun r => rootGeneratorInGroup m r.val (t r)).prod, ?_, ?_⟩
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

end ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
