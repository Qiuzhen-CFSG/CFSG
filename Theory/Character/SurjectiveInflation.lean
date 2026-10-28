module

public import Theory.Character.ClassFunction
public import Theory.Representation.Quotient

/-!
# Inflation of ordinary irreducible characters

The character of a representation pulled back along a surjection is its
pointwise pullback. Surjectivity preserves the invariant-subspace lattice,
and hence irreducibility. The groups may live in independent universes and
no finiteness hypothesis on them is needed.
-/

/-- Inflation preserves the representation-based irreducible-character predicate. -/
public theorem IsIrreducibleCharacter.comp_surjective
    {G H : Type*} [Group G] [Group H] (π : G →* H)
    (hπ : Function.Surjective π) {χ : ClassFunction H}
    (hχ : IsIrreducibleCharacter χ) : IsIrreducibleCharacter (fun g => χ (π g)) := by
  obtain ⟨n, ρ, hρ, rfl⟩ := hχ
  exact ⟨n, ρ.comp π, (Representation.irreducible_comp_surjective_iff π hπ ρ).mpr hρ, rfl⟩
