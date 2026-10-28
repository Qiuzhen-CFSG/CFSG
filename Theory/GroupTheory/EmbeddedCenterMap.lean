module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Centers of embedded subgroups

Restricting an injective group homomorphism to a subgroup gives an isomorphism
with its image. The induced isomorphism of centers commutes with the two
ambient inclusions. This lets Sylow-center calculations retain their actual
embedding when transported between models or to a larger ambient group.
-/

namespace Subgroup
variable {G H : Type*} [Group G] [Group H]
/-- Injective homomorphisms carry the whole center of a subgroup onto the whole center of its image. -/
public theorem map_embeddedCenter (R : Subgroup G) (f : G →* H) (hf : Function.Injective f) :
    ((center R).map R.subtype).map f = (center (R.map f)).map (R.map f).subtype := by
  let e := R.equivMapOfInjective f hf
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨e x, (centerCongr e ⟨x, hx⟩).property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(e.symm x : G), ⟨e.symm x, (centerCongr e.symm ⟨x, hx⟩).property, rfl⟩, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply x)
end Subgroup

