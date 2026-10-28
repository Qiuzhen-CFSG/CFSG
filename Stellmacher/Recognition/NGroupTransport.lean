module

public import Stellmacher.Recognition.NGroup

/-!
# Transport of the all-prime N condition

The N condition passes to a subgroup, more generally along any injective
group homomorphism. A nontrivial p-subgroup stays nontrivial in the image,
and its normalizer maps into the image subgroup's normalizer. Solvability
then pulls back along that injective map. Applying inheritance to both
directions of an isomorphism proves invariance under actual model recognition.
This is the normalizer condition in Thompson's definition of an N-group.
-/

namespace Stellmacher
universe u v

public theorem isNGroup_of_injective
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) (hf : Function.Injective f) (hH : IsNGroup H) : IsNGroup G := by
  intro p hp Q hQ hQp
  have hmap : Q.map f ≠ ⊥ := by
    intro heq
    apply hQ
    apply bot_unique
    intro x hx
    have hxmap : f x ∈ Q.map f := Subgroup.mem_map_of_mem f hx
    rw [heq] at hxmap
    apply hf
    simpa using hxmap
  have hpmap : IsPGroup p (Q.map f) := hQp.of_equiv (Q.equivMapOfInjective f hf)
  let := hH p hp (Q.map f) hmap hpmap
  let F : Subgroup.normalizer (Q : Set G) →*
      Subgroup.normalizer (Q.map f : Set H) :=
    (f.comp (Subgroup.normalizer (Q : Set G)).subtype).codRestrict _ (by
      intro x
      exact Q.le_normalizer_map f ⟨x, x.property, rfl⟩)
  have hF : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    exact hf (congrArg Subtype.val hxy)
  exact Group.isSolvable_of_isSolvable_injective hF

public theorem isNGroup_iff_of_mulEquiv
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) : IsNGroup G ↔ IsNGroup H := by
  exact ⟨isNGroup_of_injective e.symm.toMonoidHom e.symm.injective,
    isNGroup_of_injective e.toMonoidHom e.injective⟩

end Stellmacher
