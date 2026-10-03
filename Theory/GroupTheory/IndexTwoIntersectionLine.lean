module
public import Theory.GroupTheory.IndexTwoIntersection

/-!
# Relative index two along a crossing subgroup

Suppose A lies in X and Q, but is not contained in R, and R has relative
index two in X. Then X intersect Q intersect R has relative index two in A.
No normality in the original ambient group is required: the actual subgroup
R.subgroupOf X has index two, hence is normal in X. Apply the existing
index-two intersection theorem to A viewed in X and transport its index
back to the original ambient group. Inside A, the X and Q intersections
are redundant.

This elementary calculation supplies the line quotient used in the V0
paragraph of Stellmacher (8.2), Journal of Algebra 190 (1997), p.38;
source: `refs/latex/stellmacher-n-group.tex`.
-/

namespace Subgroup
public theorem intersection_relIndex_eq_two_of_not_le
    {G : Type*} [Group G] (X Q R A : Subgroup G)
    (hAX : A ≤ X) (hAQ : A ≤ Q) (hAR : ¬ A ≤ R)
    (hR : R.relIndex X = 2) :
    (X ⊓ Q ⊓ R).relIndex A = 2 := by
  have hn : ¬ A.subgroupOf X ≤ R.subgroupOf X := by
    intro hle
    exact hAR fun a ha => hle (show (⟨a, hAX ha⟩ : X) ∈ A.subgroupOf X from ha)
  have hi := subgroupOf_index_eq_two (R.subgroupOf X) (A.subgroupOf X) hR hn
  change (R.subgroupOf X).relIndex (A.subgroupOf X) = 2 at hi
  rw [relIndex_subgroupOf hAX] at hi
  have heq : (X ⊓ Q ⊓ R).subgroupOf A = R.subgroupOf A := by
    ext a
    change ((a : G) ∈ X ∧ (a : G) ∈ Q) ∧ (a : G) ∈ R ↔ (a : G) ∈ R
    exact ⟨fun ha => ha.2, fun ha => ⟨⟨hAX a.property, hAQ a.property⟩, ha⟩⟩
  simpa only [relIndex, heq] using hi
end Subgroup
