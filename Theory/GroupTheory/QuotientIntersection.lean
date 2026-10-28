module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Intersections with a subgroup containing a quotient kernel

If D contains the kernel of a homomorphism, intersecting its image with
the image of C is the image of C ∩ D. Taking the preimage inside C
recovers the same intersection.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, A.1.16(1).
-/

namespace Subgroup

variable {G K : Type*} [Group G] [Group K]

/-- Images preserve an intersection if the second subgroup contains the kernel. -/
public theorem map_inf_of_ker_le (f : G →* K) (C D : Subgroup G)
    (hD : f.ker ≤ D) :
    (C ⊓ D).map f = C.map f ⊓ D.map f := by
  apply le_antisymm (map_inf_le C D f)
  rintro y ⟨⟨x, hx, rfl⟩, hy⟩
  exact ⟨x, ⟨hx, show x ∈ D from (comap_map_eq_self hD) ▸ hy⟩, rfl⟩

/-- Preimage in C of the intersection of the images of C and D. -/
public theorem comap_image_inf_domRestrict (f : G →* K) (C D : Subgroup G)
    (hD : f.ker ≤ D) :
    (C.map f ⊓ D.map f).comap (f.comp C.subtype) = D.subgroupOf C := by
  ext x
  change (f (x : G) ∈ C.map f ∧ f (x : G) ∈ D.map f) ↔ (x : G) ∈ D
  have hx : f (x : G) ∈ C.map f := mem_map_of_mem f x.property
  have hd : f (x : G) ∈ D.map f ↔ (x : G) ∈ D := by
    change (x : G) ∈ (D.map f).comap f ↔ (x : G) ∈ D
    rw [comap_map_eq_self hD]
  exact and_iff_right hx |>.trans hd

end Subgroup
