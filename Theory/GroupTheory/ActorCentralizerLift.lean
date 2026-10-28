module

public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Lifting a self-centralizing actor image

Let an actor on a subgroup R have kernel contained in Q. If the image of
B ≤ R is self-centralizing in the actor range, then C_R(B) ≤ BQ. The
proof takes preimages under the actor and then returns to the ambient
group, preserving the literal subgroups.

Source application: Aschbacher--Smith 3.3.28, printed p.601.
-/

public section
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

theorem inf_centralizer_le_sup_of_actor_image
    (R B Q : Subgroup G) (hB : B ≤ R) (hQ : Q ≤ R)
    (f : R →* H) (hker : f.ker ≤ Q.subgroupOf R)
    (hself : f.range ⊓ centralizer ((B.subgroupOf R).map f : Set H) ≤
      (B.subgroupOf R).map f) :
    R ⊓ centralizer (B : Set G) ≤ B ⊔ Q := by
  intro g hg
  let r : R := ⟨g, hg.1⟩
  have himage : f r ∈ (B.subgroupOf R).map f := by
    apply hself
    refine ⟨⟨r, rfl⟩, ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    have hc : b * r = r * b := Subtype.ext (hg.2 b hb)
    exact (map_mul f b r).symm.trans
      ((congrArg f hc).trans (map_mul f r b))
  have hr : r ∈ B.subgroupOf R ⊔ f.ker := by
    rw [← comap_map_eq]
    exact himage
  have hlift : g ∈ (B.subgroupOf R ⊔ Q.subgroupOf R).map R.subtype :=
    ⟨r, (sup_le_sup_left hker _) hr, rfl⟩
  simpa only [map_sup, map_subgroupOf_eq_of_le hB,
    map_subgroupOf_eq_of_le hQ] using hlift

end Subgroup
