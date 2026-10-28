module

public import Theory.Character.ConjClassFunction
public import Theory.Representation.CharacterEquivalence

/-!
# Embeddings from actual character differences

If the difference of two complex characters is an actual character, the second
representation embeds in the first. Choose a representation of the difference;
its product with the second representation has the first representation's
character. The equal-character equivalence theorem then transports the inclusion
of the first factor to the required injective intertwiner.

Source: the character criterion for equivalence, Serre,
*Linear Representations of Finite Groups*, Chapter 2.
-/

public section

namespace Representation

/-- An actual difference of complex characters supplies an injective intertwiner. -/
theorem exists_injective_intertwiningMap_of_isConjCharacter_sub
    {G V W : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (h : IsConjCharacter (characterClassFunction ρ - characterClassFunction σ)) :
    ∃ i : σ.IntertwiningMap ρ, Function.Injective i := by
  obtain ⟨n, τ, hτ⟩ := h
  have hc : (σ.prod τ).character = ρ.character := by
    rw [character_prod]
    funext g
    have hg := congrFun hτ (ConjClasses.mk g)
    change ρ.character g - σ.character g = τ.character g at hg
    change σ.character g + τ.character g = ρ.character g
    rw [← hg]
    abel
  obtain ⟨e⟩ := equiv_of_character_eq (σ.prod τ) ρ hc
  refine ⟨e.toIntertwiningMap.comp (IntertwiningMap.inl ℂ σ τ), ?_⟩
  intro x y hxy
  have he : (x, (0 : Fin n → ℂ)) = (y, 0) := e.injective hxy
  exact congrArg Prod.fst he

end Representation
