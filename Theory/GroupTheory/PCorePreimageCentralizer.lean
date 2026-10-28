module

public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.SelfCentralizingCoreInheritance

/-!
# Self-centralizing prime cores under preimages

A surjection with p-group kernel pulls the target p-core back to the source
p-core. Consequently a self-centralizing target core gives a self-centralizing
source core. For an arbitrary map with normal range, intersect a subgroup
with that range first: characteristic p passes to this normal intersection.
This proves the preimage assertion without replacing the image by the whole
target, or discarding any part of the kernel.

Source application: the derived-model and central-cover parabolic pullbacks
in Aschbacher–Smith 2.3.9(7), printed p.526. The argument is general finite
group theory and uses the exact core lifting and normal inheritance lemmas.
-/

public section

open Subgroup
namespace MonoidHom
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
  {p : ℕ} [Fact p.Prime]

/-- Characteristic p lifts through a surjection with p-group kernel. -/
theorem centralizer_pCore_le_of_surjective_pKernel
    (f : G →* H) (hf : Function.Surjective f) (hk : IsPGroup p f.ker)
    (hc : centralizer (pCore p H : Set H) ≤ pCore p H) :
    centralizer (pCore p G : Set G) ≤ pCore p G := by
  have he := f.comap_pCore_of_ker_isPGroup hf hk
  have hm : (pCore p G).map f = pCore p H := by
    rw [← he, map_comap_eq_self]
    rw [f.range_eq_top_of_surjective hf]
    exact le_top
  intro x hx
  rw [← he]
  apply hc
  rw [← hm]
  rintro y ⟨a, ha, rfl⟩
  simpa only [← map_mul] using congrArg f (hx a ha)

/-- Restrict the homomorphism to the subgroup and its actual image. -/
theorem centralizer_pCore_subgroup_of_image
    (f : G →* H) (hk : IsPGroup p f.ker) (P : Subgroup G)
    (hc : centralizer (pCore p (P.map f) : Set (P.map f)) ≤ pCore p (P.map f)) :
    centralizer (pCore p P : Set P) ≤ pCore p P := by
  apply centralizer_pCore_le_of_surjective_pKernel (f.subgroupMap P)
    (f.subgroupMap_surjective P) _ hc
  rw [Subgroup.ker_subgroupMap]
  exact hk.comap_subtype

end MonoidHom

namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Intersecting with an ambient normal subgroup preserves characteristic p. -/
theorem inf_normal_core_selfCentralizing (P N : Subgroup G) [N.Normal]
    (hc : centralizer (pCore p P : Set P) ≤ pCore p P) :
    centralizer (pCore p (P ⊓ N : Subgroup G) : Set (P ⊓ N : Subgroup G)) ≤
      pCore p (P ⊓ N : Subgroup G) := by
  let e : (P ⊓ N : Subgroup G) ≃* N.subgroupOf P :=
    { toFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
      invFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  exact (Theory.Quasithin.centralizer_pCore_le_iff p e).mpr
    (normal_core_selfCentralizing hc (N.subgroupOf P))
end Subgroup

namespace MonoidHom
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
  {p : ℕ} [Fact p.Prime]

/-- Pull back through a p-group kernel, retaining the normal actual range. -/
theorem centralizer_pCore_comap_of_normal_range
    (f : G →* H) [f.range.Normal] (hk : IsPGroup p f.ker) (P : Subgroup H)
    (hc : centralizer (pCore p P : Set P) ≤ pCore p P) :
    centralizer (pCore p (P.comap f) : Set (P.comap f)) ≤ pCore p (P.comap f) := by
  apply f.centralizer_pCore_subgroup_of_image hk (P.comap f)
  rw [Subgroup.map_comap_eq, inf_comm]
  exact Subgroup.inf_normal_core_selfCentralizing P f.range hc

end MonoidHom

end
