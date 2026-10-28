module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.FiniteCover

/-!
# The two-place geometry

For two subgroups P,Q the leaf intersection is automatic. If x lies in P,
y lies in Q and their product lies in P or Q, cancellation puts both
elements in that same subgroup. This settles pattern 9 without computation.
Application: the marked Parrott parabolics, Parrott (1972), p.683.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups

private theorem pair_leafIntersections {G : Type*} [Group G] (P Q : Subgroup G) :
    LeafIntersections [P, Q] := by
  apply LeafIntersections.cons P Q [Q] (by simp) ?_ (LeafIntersections.singleton Q)
  intro R hR
  obtain rfl := List.mem_singleton.mp hR
  exact inf_le_right

private theorem pair_productCompatible {G : Type*} [Group G] (P Q : Subgroup G) :
    ProductCompatible [P, Q] := by
  intro x y hx hy hxy
  have hx' : x ∈ P ∨ x ∈ Q := by simpa using hx
  have hy' : y ∈ P ∨ y ∈ Q := by simpa using hy
  have hxy' : x * y ∈ P ∨ x * y ∈ Q := by simpa using hxy
  suffices (x ∈ P ∧ y ∈ P) ∨ (x ∈ Q ∧ y ∈ Q) by simpa using this
  rcases hx' with hx | hx
  · rcases hy' with hy | hy
    · exact Or.inl ⟨hx, hy⟩
    · rcases hxy' with hxy | hxy
      · exact Or.inl ⟨hx, by
          simpa only [inv_mul_cancel_left] using P.mul_mem (P.inv_mem hx) hxy⟩
      · exact Or.inr ⟨by
          simpa only [mul_inv_cancel_right] using Q.mul_mem hxy (Q.inv_mem hy), hy⟩
  · rcases hy' with hy | hy
    · rcases hxy' with hxy | hxy
      · exact Or.inl ⟨by
          simpa only [mul_inv_cancel_right] using P.mul_mem hxy (P.inv_mem hy), hy⟩
      · exact Or.inr ⟨hx, by
          simpa only [inv_mul_cancel_left] using Q.mul_mem (Q.inv_mem hx) hxy⟩
    · exact Or.inr ⟨hx, hy⟩

/-- The two marked parabolics have the required intersection geometry. -/
theorem placePattern_nine_leafIntersections :
    LeafIntersections ((placePattern 9).map place) :=
  pair_leafIntersections (place 0) (place 17)

/-- The two marked parabolics have compatible products in their union. -/
theorem placePattern_nine_productCompatible :
    ProductCompatible ((placePattern 9).map place) :=
  pair_productCompatible (place 0) (place 17)

/-- A subgroup covered by the two marked places lies in one of them. -/
theorem placePattern_nine_le_of_union (K : Subgroup Atlas1600Group)
    (hcover : ∀ x ∈ K, ∃ P ∈ (placePattern 9).map place, x ∈ P) :
    ∃ P ∈ (placePattern 9).map place, K ≤ P :=
  le_of_union placePattern_nine_leafIntersections placePattern_nine_productCompatible K hcover

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups
