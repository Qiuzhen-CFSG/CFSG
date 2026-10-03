module

public import Theory.Character.ModularBlock.PrincipalKernel
public import Theory.Character.Inflation

/-!
# Descent of principal-block characters to the odd-core quotient

Every character in the principal two-block is the inflation of an actual
irreducible character of the quotient by the odd core. The principal-block
kernel theorem factors a realizing representation through this quotient;
invariance of the character inner product under inflation proves irreducibility.
This assertion concerns ordinary characters and does not assert the converse
block-membership statement.

Source: Feit, IV.4.12(ii); ABG III.2 Proposition 7.
-/

namespace ModularBlock.PrincipalBlockKernel
open PrincipalBlockConstruction
noncomputable section

/-- Descend a principal-block row to the actual odd-core quotient, retaining
its irreducible character and its inflation identity. -/
public theorem exists_quotient_character_of_mem_block
    {G : Type*} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) {i : d.I} (hi : i ∈ d.block) :
    ∃ χ : ConjClassFunction (G ⧸ pPrimeCore 2 G),
      IsIrreducibleConjCharacter χ ∧
        d.chi i = χ ∘ ConjClasses.map (QuotientGroup.mk' (pPrimeCore 2 G)) := by
  obtain ⟨n, ρ, hρ⟩ := (d.complete.1 i).1
  let σ : Representation ℂ (G ⧸ pPrimeCore 2 G) (Fin n → ℂ) :=
    QuotientGroup.lift (pPrimeCore 2 G) ρ
      (pPrimeCore_le_representation_ker_of_mem_block d hi ρ hρ)
  have he : d.chi i = characterClassFunction σ ∘
      ConjClasses.map (QuotientGroup.mk' (pPrimeCore 2 G)) := by
    funext c
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
    rw [hρ]
    rfl
  refine ⟨characterClassFunction σ, ⟨⟨n, σ, rfl⟩, ?_⟩, he⟩
  rw [← classFunctionInner_comp_surjective
    (QuotientGroup.mk' (pPrimeCore 2 G))
    (QuotientGroup.mk'_surjective (pPrimeCore 2 G)), ← he]
  exact (d.complete.1 i).2

end
end ModularBlock.PrincipalBlockKernel
