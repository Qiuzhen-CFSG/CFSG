module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Actors.FixedBounds.CatalogueCoverage.Code

/-!
# Completeness by adjoining commuting involutions

A table containing the identity row and stable under elementary extensions
covers every finite elementary subgroup: take a largest row inside that
subgroup and adjoin any missing element. The accompanying subsequence-product
bounds convert a generator list into the cardinal estimate used for binary rank.

This is the abstract finite-checking argument for the standard adjoint actor
catalogue, not a claim that its concrete extension checks have been discharged.
Source application: Guralnick–Malle Lemma 4.5 and Proposition 4.8 step 3A;
Aschbacher–Smith K.3.2, printed pp.454–455.
-/

@[expose] public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.FixedBounds
namespace CoverageCode

variable {C : Type*} [DecidableEq C] (z : C) (op : C → C → C)

/-- All ordered products of subsequences, including the empty product. -/
def products : List C → Finset C
  | [] => {z}
  | a :: l => products l ∪ (products l).image (op a)

theorem zero_mem_products (l : List C) : z ∈ products z op l := by
  induction l with
  | nil => exact Finset.mem_singleton_self z
  | cons a l ih => exact Finset.mem_union_left _ ih

theorem mem_products_of_mem (hz : ∀ x, op x z = x) {l : List C} {a : C}
    (ha : a ∈ l) : a ∈ products z op l := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨z, zero_mem_products z op l, hz a⟩)
    · exact Finset.mem_union_left _ (ih ha)

theorem card_products_le (l : List C) : (products z op l).card ≤ 2 ^ l.length := by
  induction l with
  | nil => simp [products]
  | cons a l ih =>
    have hu := Finset.card_union_le (products z op l) ((products z op l).image (op a))
    have hi := Finset.card_image_le (s := products z op l) (f := op a)
    simp only [products, List.length_cons, pow_succ]
    omega

/-- A finite table containing the identity and stable under adjoining commuting
involutions contains every finite elementary multiplication-closed set. This
uses a largest contained row, not enumeration of all subsets of the carrier. -/
theorem exists_row_of_extensions {I : Type*} [Fintype I]
    (rows : I → Finset C) (base : I) (hbase : rows base = {z})
    (hzero : ∀ i, z ∈ rows i) (hright : ∀ x, op x z = x)
    (hext : ∀ i x, op x x = z → (∀ a ∈ rows i, op x a = op a x) →
      ∃ j, rows j = rows i ∪ (rows i).image (op x))
    (T : Finset C) (hzT : z ∈ T)
    (hclosed : ∀ x ∈ T, ∀ y ∈ T, op x y ∈ T)
    (hsq : ∀ x ∈ T, op x x = z)
    (hcomm : ∀ x ∈ T, ∀ y ∈ T, op x y = op y x) :
    ∃ i, rows i = T := by
  classical
  let candidates := Finset.univ.filter (fun i => rows i ⊆ T)
  have hb : base ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and, hbase]
    exact Finset.singleton_subset_iff.mpr hzT
  obtain ⟨i, hi, hmax⟩ := candidates.exists_max_image (fun j => (rows j).card) ⟨base, hb⟩
  have hiT : rows i ⊆ T := (Finset.mem_filter.mp hi).2
  refine ⟨i, Finset.Subset.antisymm hiT ?_⟩
  intro x hx
  obtain ⟨j, hj⟩ := hext i x (hsq x hx) (fun a ha => hcomm x hx a (hiT ha))
  have hjT : rows j ⊆ T := by
    rw [hj]
    refine Finset.union_subset hiT ?_
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    exact hclosed x hx a (hiT ha)
  have hjc : j ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjT⟩
  have hij : rows i ⊆ rows j := by rw [hj]; exact Finset.subset_union_left
  have heq : rows i = rows j := Finset.eq_of_subset_of_card_le hij (hmax j hjc)
  rw [heq, hj]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z, hzero i, hright x⟩)

end CoverageCode
end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.FixedBounds
