module

public import Theory.Representation.IrreducibleTraceEquivalence
public import Theory.Representation.PRegularTrace

/-!
# Irreducibles determined by traces on p-regular elements

Over an algebraically closed field of characteristic p, equality of traces on
p-regular elements determines a finite-dimensional irreducible representation.
The p-part reduction chooses, for each group element, one p-regular element
with the same trace simultaneously in both representations. Simple-module
density then turns equality of the full trace functions into an intertwiner.
No invertibility of the group order or semisimplicity assumption is needed.

This is the trace comparison used after the characteristic-eleven calculation
in Janko's argument; see Gorenstein, *Finite Groups*, §16.6, p.482.
-/

namespace Representation

universe u

/-- Traces on p-regular elements suffice to compare irreducibles, including
when p divides the group order. -/
public theorem pRegular_character_eq_iff_equiv_of_irreducible
    {F G : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    {V W : Type u} [AddCommGroup V] [AddCommGroup W]
    [Module F V] [Module F W] [FiniteDimensional F V] [FiniteDimensional F W]
    (ρ : Representation F G V) (σ : Representation F G W)
    [IsIrreducible ρ] [IsIrreducible σ] :
    (∀ g : G, ¬ p ∣ orderOf g → ρ.character g = σ.character g) ↔
      Nonempty (ρ.Equiv σ) := by
  constructor
  · intro h
    apply (character_eq_iff_equiv_of_irreducible ρ σ).mp
    funext g
    obtain ⟨x, hx, htrace⟩ := exists_pRegular_same_character (F := F) p g
    exact (htrace V ρ).trans ((h x hx).trans (htrace W σ).symm)
  · rintro ⟨e⟩ g _
    exact congrFun (char_iso e) g

end Representation
