module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.Basic
public import Theory.GroupTheory.FilteredCollection

/-!
# Collecting the actual split F4 root words

Subgroup closure induction writes every element of each split subgroup as a
finite word in its supported root matrices. Inverses are absorbed by negating
parameters. The filtered collection theorem then puts this word in any chosen
root order, provided the actual matrices satisfy adjacent exchanges with
corrections strictly above both exchanged heights.

The exchange formula is an explicit remaining premise, not an assertion that
the subgroup already has ordered coordinates. This module proves the
group-theoretic completeness step of the Chevalley construction underlying
Aschbacher–Smith F.1.12(I)(5), printed p.263 of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section

namespace ReeF4.Parabolics.RadicalCoordinates

open Theory.AlgebraicGroup StandardRootSystem
open FilteredCollection

private theorem factor_add (m : ℕ) (r : F4Chevalley.Root)
    (a b : CoefficientField m) :
    rootGeneratorInGroup m r a * rootGeneratorInGroup m r b =
      rootGeneratorInGroup m r (a + b) := by
  apply Subtype.ext
  exact (F4Chevalley.rootCurve_add r a b).symm

private theorem factor_inv (m : ℕ) (r : F4Chevalley.Root)
    (a : CoefficientField m) :
    (rootGeneratorInGroup m r a)⁻¹ = rootGeneratorInGroup m r (-a) := by
  apply Subtype.ext
  exact F4Chevalley.rootCurve_inv r a

/-- The same generating set, with the support condition carried by the root type. -/
theorem splitSubgroup_eq_closure (m : ℕ) (k : Support) :
    splitSubgroup m k = Subgroup.closure
      {x | ∃ (r : Root k) (t : CoefficientField m),
        x = rootGeneratorInGroup m r.val t} := by
  cases k <;> apply congrArg Subgroup.closure
  all_goals ext x; constructor
  all_goals
    first
    | rintro ⟨r, t, hr, rfl⟩; exact ⟨⟨r, hr⟩, t, rfl⟩
    | rintro ⟨r, t, rfl⟩; exact ⟨r.val, t, r.property, rfl⟩

private theorem rootWord_inv (m : ℕ) {k : Support}
    (w : List (Root k × CoefficientField m)) :
    (wordProduct (fun r : Root k => rootGeneratorInGroup m r.val) w)⁻¹ =
      wordProduct (fun r : Root k => rootGeneratorInGroup m r.val)
        (w.reverse.map (fun z => (z.1, -z.2))) := by
  induction w with
  | nil => simp [wordProduct]
  | cons z w ih =>
      simpa only [wordProduct, List.map_cons, List.prod_cons,
        List.reverse_cons, List.map_append, List.map_map, List.prod_append,
        List.map_nil, List.prod_nil, mul_one, Function.comp_def,
        mul_inv_rev, factor_inv] using congrArg
          (fun y => y * rootGeneratorInGroup m z.1.val (-z.2)) ih

/-- Every element is a finite supported root word; no collection is used here. -/
theorem exists_rootWord (m : ℕ) {k : Support} (x : SplitGroup m)
    (hx : x ∈ splitSubgroup m k) :
    ∃ w : List (Root k × CoefficientField m),
      x = wordProduct (fun r : Root k => rootGeneratorInGroup m r.val) w := by
  classical
  rw [splitSubgroup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
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
      exact ⟨w.reverse.map (fun z => (z.1, -z.2)), rootWord_inv m w⟩

/-- Exact adjacent exchanges suffice for completeness in every root ordering. -/
theorem wordInSubgroup_surjective_of_exchange (m : ℕ) {k : Support}
    (hswap : ∀ (r s : Root k) (a b : CoefficientField m), r ≠ s →
      ∃ correction : List (Root k × CoefficientField m),
        (∀ z ∈ correction,
          max (rootDegree r.val) (rootDegree s.val) < rootDegree z.1.val) ∧
        rootGeneratorInGroup m r.val a * rootGeneratorInGroup m s.val b =
          rootGeneratorInGroup m s.val b * rootGeneratorInGroup m r.val a *
            wordProduct (fun q : Root k => rootGeneratorInGroup m q.val) correction)
    (e : RootOrder k) : Function.Surjective (wordInSubgroup m e) := by
  classical
  let : Fintype (Root k) := Fintype.ofFinite _
  let order := List.ofFn e
  have hmem (r : Root k) : r ∈ order := List.mem_ofFn.mpr (e.surjective r)
  intro x
  obtain ⟨w, hw⟩ := exists_rootWord m x.val x.property
  obtain ⟨t, ht⟩ := filteredCollection_exists_params
    (fun r : Root k => rootDegree r.val)
    (fun r : Root k => rootGeneratorInGroup m r.val) order
    (List.nodup_ofFn.mpr e.injective)
    ((Finset.univ.sup fun r : Root k => rootDegree r.val) + 1)
    (fun r _ => Nat.lt_succ_of_le (Finset.le_sup (f := fun r : Root k =>
      rootDegree r.val) (Finset.mem_univ r)))
    (fun r a b => factor_add m r.val a b)
    (fun r s a b _ _ hne => by
      obtain ⟨c, hc, he⟩ := hswap r s a b hne
      exact ⟨c, fun z hz => ⟨hmem z.1, hc z hz⟩, he⟩)
    w (fun z _ => hmem z.1)
  refine ⟨t, Subtype.ext ?_⟩
  change word m e t = x.val
  rw [hw, ht]
  simp only [word, order, List.map_ofFn, Function.comp_def]

end ReeF4.Parabolics.RadicalCoordinates
