module

public import Theory.GroupTheory.ConjugationLocalGeometry
public import Mathlib.GroupTheory.PGroup

/-!
# Pairs with order-two images

Different order-two image subgroups intersect trivially, so the original
intersection lies in the kernel. Equal images generate a two-group when
the kernel is a two-group. These alternatives use the given homomorphism;
no replacement of a subgroup image by its own core quotient is made.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
13.5.13, printed p.919. The chapter application uses H → H/O₂(H).
-/

public section
namespace Subgroup
variable {G J : Type*} [Group G] [Group J]

/-- Distinct order-two images force the intersection into the actual kernel. -/
theorem inf_le_ker_of_distinct_order_two_images (f : G →* J) (A B : Subgroup G)
    (ha : Nat.card (A.map f) = 2) (hb : Nat.card (B.map f) = 2)
    (hne : A.map f ≠ B.map f) : A ⊓ B ≤ f.ker := by
  intro x hx
  have hm : f x ∈ A.map f ⊓ B.map f :=
    ⟨mem_map_of_mem f hx.1, mem_map_of_mem f hx.2⟩
  rw [inf_eq_bot_of_card_two_of_ne _ _ ha hb hne] at hm
  exact hm

/-- Equal order-two images and a two-group kernel give a two-group join. -/
theorem isTwoGroup_sup_of_equal_order_two_images (f : G →* J) (A B : Subgroup G)
    (hk : IsPGroup 2 f.ker) (ha : Nat.card (A.map f) = 2)
    (he : A.map f = B.map f) : IsPGroup 2 (A ⊔ B : Subgroup G) := by
  have hp : IsPGroup 2 (A.map f) := IsPGroup.of_card (n := 1) (by simpa using ha)
  apply (hp.comap_of_ker_isPGroup f hk).to_le
  apply map_le_iff_le_comap.mp
  rw [map_sup, ← he, sup_idem]

end Subgroup

end
