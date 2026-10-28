module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

/-!
# An inverted subgroup of index two

If an element outside an abelian subgroup of index two inverts that subgroup,
every outside element has the same action and the same square. In particular,
an outside involution establishes splitting; the existence of an inverter
alone does not establish it.

Write another outside element as `a * t`, with `a` in the subgroup, and use
`t * a * t⁻¹ = a⁻¹`. This is the elementary calculation needed to select the
inverter in Stellmacher (8.6)(a), `refs/latex/stellmacher-n-group.tex`.
-/

namespace Subgroup

/-- Every element outside an inverted index-two subgroup has the same square
as the chosen outside inverter. -/
public theorem sq_eq_of_inverted_index_two
    {G : Type*} [Group G] (A : Subgroup G) (hindex : A.index = 2)
    {t x : G} (ht : t ∉ A) (hx : x ∉ A)
    (hinv : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹) : x ^ 2 = t ^ 2 := by
  have ha : x * t⁻¹ ∈ A :=
    (A.mul_mem_iff_of_index_two hindex).mpr
      (by simp only [hx, A.inv_mem_iff, ht])
  have h := hinv (x * t⁻¹) ha
  calc
    x ^ 2 = (x * t⁻¹) * (t * (x * t⁻¹) * t⁻¹) * t ^ 2 := by
      simp only [pow_two]
      group
    _ = (x * t⁻¹) * (x * t⁻¹)⁻¹ * t ^ 2 := by rw [h]
    _ = t ^ 2 := by group

/-- Every element outside an abelian index-two subgroup acts by inversion
when one outside element does. -/
public theorem inverts_of_inverted_index_two
    {G : Type*} [Group G] (A : Subgroup G) (hindex : A.index = 2)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {t x : G} (ht : t ∉ A) (hx : x ∉ A)
    (hinv : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹) :
    ∀ a ∈ A, x * a * x⁻¹ = a⁻¹ := by
  have hb : x * t⁻¹ ∈ A :=
    (A.mul_mem_iff_of_index_two hindex).mpr
      (by simp only [hx, A.inv_mem_iff, ht])
  intro a ha
  calc
    x * a * x⁻¹ = (x * t⁻¹) * (t * a * t⁻¹) * (x * t⁻¹)⁻¹ := by group
    _ = (x * t⁻¹) * a⁻¹ * (x * t⁻¹)⁻¹ := by rw [hinv a ha]
    _ = a⁻¹ * (x * t⁻¹) * (x * t⁻¹)⁻¹ := by
      rw [hcomm _ hb _ (A.inv_mem ha)]
    _ = a⁻¹ := by group

end Subgroup
