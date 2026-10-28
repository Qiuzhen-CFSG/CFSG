module

public import Theory.SpecificGroups.ReeF4.DerivedTits.BruhatBound.Cells
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders

/-!
# Counting the restricted binary Ree Bruhat cells

Restricted fixed-point Bruhat coverage gives a surjection from the disjoint
union of `U × U_w` over the sixteen concrete Weyl representatives. `Geometry`
proves their coverage by their actual F₄ root actions. `Cells` bounds each
right factor using complementary positive blocks and disjointness of opposite
unipotent subgroups. Their bounds sum to 8775.

Together with the proved order `|U| = 4096`, this gives the unconditional
upper bound 35942400 for the full exceptional fixed matrix carrier, and hence
`binary_card_lt`, the strict bound used by the derived-group comparison.
No presentation realization or derived-group equivalence is used. The
conditional counting lemmas are retained as reusable reductions.

Sources: GLS3 §§2.3.2–2.3.8 and Table 2.4, `refs/KGroup/GLS3/chapter2.tex`;
Aschbacher–Smith F.1.12(I)(5), printed pp.263–264 of `refs/quasithin.pdf`.
-/

public section
noncomputable section

namespace ReeF4.DerivedTits

open Parabolics Parabolics.Binary.FixedGeometry BruhatBound

/-- Count restricted cells using any finite covering family of actual Weyl
representatives. Repetitions in the family do not affect the upper bound. -/
theorem binary_card_le_of_weyl_cover {ι : Type*} [Fintype ι]
    (n : ι → Model 0)
    (hcover : ∀ w ∈ weylSubgroup 0, ∃ i, n i = w) :
    Nat.card (Model 0) ≤ 4096 * ∑ i, Nat.card (fixedRightUnipotent (n i)) := by
  let f : (Σ i, (unipotent 0) × fixedRightUnipotent (n i)) → Model 0 :=
    fun x => x.2.1.val * n x.1 * x.2.2.val
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨u, hu, w, hw, v, hv, he⟩ := exists_restricted_normal_form g
    obtain ⟨i, rfl⟩ := hcover w hw
    exact ⟨⟨i, ⟨⟨u, hu⟩, ⟨v, hv⟩⟩⟩, he.symm⟩
  have hU : Nat.card (unipotent 0) = 4096 := by
    simpa using card_unipotent 0
  calc
    Nat.card (Model 0) ≤ Nat.card (Σ i, (unipotent 0) × fixedRightUnipotent (n i)) :=
      Nat.card_le_card_of_surjective f hf
    _ = 4096 * ∑ i, Nat.card (fixedRightUnipotent (n i)) := by
      simp only [Nat.card_sigma, Nat.card_prod, hU, Finset.mul_sum]

/-- Conditional numerical bound from coverage and the sixteen restricted-cell
estimates. Both premises concern the actual fixed matrix carrier. -/
theorem binary_card_le_of_weyl_cover_of_cell_bounds
    (hcover : ∀ w ∈ weylSubgroup 0, ∃ i, weylRepresentative i = w)
    (hcell : ∀ i, Nat.card (fixedRightUnipotent (weylRepresentative i)) ≤
      2 ^ cellExponent i) : Nat.card (Model 0) ≤ 35942400 := by
  calc
    Nat.card (Model 0) ≤ 4096 *
        ∑ i, Nat.card (fixedRightUnipotent (weylRepresentative i)) :=
      binary_card_le_of_weyl_cover weylRepresentative hcover
    _ ≤ 4096 * ∑ i : Fin 16, 2 ^ cellExponent i := by
      exact Nat.mul_le_mul_left _ (Finset.sum_le_sum (fun i _ => hcell i))
    _ = 35942400 := by rw [sum_cell_bounds]

/-- The precise strict inequality consumed by the derived-group comparison,
still conditional on the Weyl cover and the restricted-cell estimates. -/
theorem binary_card_lt_of_weyl_cover_of_cell_bounds
    (hcover : ∀ w ∈ weylSubgroup 0, ∃ i, weylRepresentative i = w)
    (hcell : ∀ i, Nat.card (fixedRightUnipotent (weylRepresentative i)) ≤
      2 ^ cellExponent i) : Nat.card (Model 0) < 3 * 17971200 := by
  have h := binary_card_le_of_weyl_cover_of_cell_bounds hcover hcell
  omega

/-- The full binary Ree fixed matrix carrier has at most 35942400 elements. -/
theorem binary_card_le : Nat.card (Model 0) ≤ 35942400 :=
  binary_card_le_of_weyl_cover_of_cell_bounds weylRepresentative_cover
    fixedRightUnipotent_card_le

/-- The ambient size bound needed to identify a nontrivial Tits image with the
derived subgroup. This concerns the full `Model 0`, without a realization premise. -/
theorem binary_card_lt : Nat.card (Model 0) < 3 * 17971200 := by
  have h := binary_card_le
  omega

end ReeF4.DerivedTits
