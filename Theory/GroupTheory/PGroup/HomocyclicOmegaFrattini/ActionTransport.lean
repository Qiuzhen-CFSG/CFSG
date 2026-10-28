module

public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Transport of actual automorphism actions

An equivariant group isomorphism identifies action kernels, invariant
subgroups and action images. The range isomorphism is conjugation of
automorphisms by the given isomorphism. These elementary transport facts
are used by the homocyclic power bridge and the A.3.6 core actions.
-/

@[expose] public section
open Subgroup

namespace GroupActionTransport
variable {A X Y : Type*} [Group A] [Group X] [Group Y]
    (ρ : A →* MulAut X) (τ : A →* MulAut Y) (e : X ≃* Y)
    (he : ∀ a x, e (ρ a x) = τ a (e x))

include he in
theorem equivariant_ker_eq : ρ.ker = τ.ker := by
  ext a
  simp only [MonoidHom.mem_ker]
  constructor
  · intro ha
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    simpa only [ha, MulAut.one_apply] using (he a x).symm
  · intro ha
    apply MulEquiv.ext
    intro x
    apply e.injective
    simpa only [ha, MulAut.one_apply] using he a x

include he in
theorem equivariant_irreducible
    (hi : ∀ B : Subgroup Y, (∀ a y, y ∈ B → τ a y ∈ B) → B = ⊥ ∨ B = ⊤) :
    ∀ B : Subgroup X, (∀ a x, x ∈ B → ρ a x ∈ B) → B = ⊥ ∨ B = ⊤ := by
  intro B hB
  have hmap : ∀ a y, y ∈ B.map e.toMonoidHom → τ a y ∈ B.map e.toMonoidHom := by
    rintro a y ⟨x, hx, rfl⟩
    exact ⟨ρ a x, hB a x hx, he a x⟩
  rcases hi _ hmap with hb | ht
  · exact Or.inl ((B.map_eq_bot_iff_of_injective e.injective).mp hb)
  · right
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_top_of_surjective e.toMonoidHom e.surjective]
    exact ht

noncomputable def equivariantRangeEquiv : ρ.range ≃* τ.range := by
  let f := MulAut.congr e
  have hc : f.toMonoidHom.comp ρ = τ := by
    ext a y
    obtain ⟨x, rfl⟩ := e.surjective y
    simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.congr_apply, MulEquiv.trans_apply, e.symm_apply_apply] using he a x
  have hr : ρ.range.map f.toMonoidHom = τ.range := by
    rw [← MonoidHom.range_comp, hc]
  exact (ρ.range.equivMapOfInjective f.toMonoidHom f.injective).trans
    (MulEquiv.subgroupCongr hr)
end GroupActionTransport
