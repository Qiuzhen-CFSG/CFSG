module

public import Theory.GroupTheory.PGroup.Omega

/-!
# Omega under faithful ambient embeddings

Two injective group homomorphisms with the same ambient image carry their
omega subgroups to the same subgroup. This allows omega to be transported
between different subgroup realizations while retaining the ambient maps.

Map the defining closure through each homomorphism. Injectivity identifies
the power-trivial generators in each domain with the same ambient elements.
This is a direct consequence of the definition of omega.
-/

namespace Subgroup

/-- Equal faithful ambient images give equal ambient omega subgroups. -/
public theorem map_omega_eq_of_injective_of_range_eq
    {A B G : Type*} [Group A] [Group B] [Group G]
    (f : A →* G) (g : B →* G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) (p k : ℕ) :
    (omega A (p := p) k).map f = (omega B (p := p) k).map g := by
  change (closure {a : A | a ^ (p ^ k) = 1}).map f =
    (closure {b : B | b ^ (p ^ k) = 1}).map g
  rw [MonoidHom.map_closure, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨b, hb⟩ := h ▸ (show f a ∈ f.range from ⟨a, rfl⟩)
    refine ⟨b, ?_, hb⟩
    apply hg
    simpa only [map_pow, map_one, hb] using congrArg f ha
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨a, ha⟩ := h.symm ▸ (show g b ∈ g.range from ⟨b, rfl⟩)
    refine ⟨a, ?_, ha⟩
    apply hf
    simpa only [map_pow, map_one, ha] using congrArg g hb

end Subgroup

/-- An isomorphism carries each omega subgroup onto the corresponding omega
subgroup. -/
public theorem MulEquiv.map_omega
    {A B : Type*} [Group A] [Group B] (e : A ≃* B) (p k : ℕ) :
    (omega A (p := p) k).map e.toMonoidHom = omega B (p := p) k := by
  simpa using Subgroup.map_omega_eq_of_injective_of_range_eq
    e.toMonoidHom (MonoidHom.id B) e.injective Function.injective_id
    (by rw [MonoidHom.range_eq_top.mpr e.surjective,
      MonoidHom.range_eq_top.mpr Function.surjective_id]) p k

/-- The restriction of an isomorphism to omega subgroups. -/
public noncomputable def MulEquiv.omega
    {A B : Type*} [Group A] [Group B] (e : A ≃* B) (p k : ℕ) :
    _root_.omega A (p := p) k ≃* _root_.omega B (p := p) k :=
  (e.subgroupMap (_root_.omega A (p := p) k)).trans
    (MulEquiv.subgroupCongr (e.map_omega p k))
