module

public import Theory.Representation.Quotient

/-!
# Representations under a group isomorphism

Precomposition with a group isomorphism gives a bijection of representations
on the same vector space. The invariant-subspace lattice is unchanged, and
injectivity is preserved in both directions. Hence it gives a bijection of
faithful irreducibles, preserving the field, vector space and dimension.

The final theorem transports a universal degree bound. This applies only
once an actual isomorphism of the acting groups has been supplied.

Source: the inflation/descent construction in `Theory.Representation.Quotient`;
GLS3 §2.8 uses it when passing between versions of a finite group of Lie type.
-/

@[expose] public section

namespace Representation

variable {F G H V : Type*} [Field F] [Group G] [Group H]
  [AddCommGroup V] [Module F V]

/-- Change the acting group, keeping the vector space and scalar action. -/
def groupEquivalence (e : G ≃* H) : Representation F H V ≃ Representation F G V where
  toFun ρ := ρ.comp e.toMonoidHom
  invFun σ := σ.comp e.symm.toMonoidHom
  left_inv ρ := by ext g v; simp
  right_inv σ := by ext g v; simp

/-- Faithfulness is invariant under an isomorphism of the acting groups. -/
theorem injective_comp_mulEquiv_iff (e : G ≃* H) (ρ : Representation F H V) :
    Function.Injective (ρ.comp e.toMonoidHom) ↔ Function.Injective ρ := by
  constructor
  · intro h x y hxy
    have : e.symm x = e.symm y := h (by simpa using hxy)
    exact e.symm.injective this
  · intro h
    exact h.comp e.injective

/-- The correspondence of faithful irreducibles on the same vector space. -/
def faithfulIrreducibleGroupEquivalence (e : G ≃* H) :
    {ρ : Representation F H V // ρ.IsIrreducible ∧ Function.Injective ρ} ≃
      {σ : Representation F G V // σ.IsIrreducible ∧ Function.Injective σ} where
  toFun ρ := ⟨ρ.val.comp e.toMonoidHom,
    (irreducible_comp_surjective_iff e.toMonoidHom e.surjective ρ.val).mpr ρ.property.1,
    (injective_comp_mulEquiv_iff e ρ.val).mpr ρ.property.2⟩
  invFun σ := ⟨σ.val.comp e.symm.toMonoidHom,
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective σ.val).mpr
      σ.property.1,
    (injective_comp_mulEquiv_iff e.symm σ.val).mpr σ.property.2⟩
  left_inv ρ := Subtype.ext ((groupEquivalence e).left_inv ρ.val)
  right_inv σ := Subtype.ext ((groupEquivalence e).right_inv σ.val)

/-- A universal lower bound on degrees transfers in either direction. -/
theorem forall_faithful_irreducible_finrank_ge_iff (e : G ≃* H) (d : ℕ) :
    (∀ ρ : Representation F G V, ρ.IsIrreducible → Function.Injective ρ →
      d ≤ Module.finrank F V) ↔
    (∀ σ : Representation F H V, σ.IsIrreducible → Function.Injective σ →
      d ≤ Module.finrank F V) := by
  constructor
  · intro h σ hi hf
    have hσ := faithfulIrreducibleGroupEquivalence e ⟨σ, hi, hf⟩
    exact h hσ.val hσ.property.1 hσ.property.2
  · intro h ρ hi hf
    have hρ := faithfulIrreducibleGroupEquivalence e.symm ⟨ρ, hi, hf⟩
    exact h hρ.val hρ.property.1 hρ.property.2

end Representation
