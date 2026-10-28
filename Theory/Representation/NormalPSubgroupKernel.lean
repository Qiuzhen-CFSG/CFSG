module

public import Theory.Representation.NormalInvariants
public import Theory.Representation.TwoDimensionalOddOrder

/-!
# Normal p-subgroups in modular irreducible representations

A normal p-subgroup of a finite group acts trivially on every finite-dimensional
irreducible representation in characteristic p. The p-group fixed-vector theorem
provides a nonzero invariant; normality makes the fixed space an ambient
subrepresentation, and irreducibility makes it the whole representation.

This extends the private prime-field argument in
`Theory.Representation.IrreducibleNonPConjugatePair` to arbitrary fields.
-/

namespace Representation

public theorem normal_p_subgroup_le_ker
    {F H V : Type*} [Field F] [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] [CharP F p]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F H V) [IsIrreducible ρ]
    (N : Subgroup H) [N.Normal] (hN : IsPGroup p N) : N ≤ ρ.ker := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  have hc : ringChar F = p := ringChar.eq F p
  obtain ⟨v, hv, hfix⟩ := pGroup_fix_nonzero_vector
    (hc ▸ (Fact.out : p.Prime).ne_zero) (hc.symm ▸ hN) (ρ.comp N.subtype)
  apply le_ker_of_normal_invariants_ne_bot ρ N
  intro hbot
  have hmem : v ∈ invariants (ρ.comp N.subtype) := hfix
  rw [hbot, Submodule.mem_bot] at hmem
  exact hv hmem

end Representation
