module
public import Theory.Representation.SL2.PrimeFieldParameters.Unsigned

/-!
# Irreducibility at the minimum binary SL₂ degree

A fixed-point-free binary module of SL₂(2ⁿ), of dimension at most 2n,
is irreducible. Choose a simple submodule. Its action cannot be trivial,
since the original invariant space is zero, and the prime-field degree
bound makes its dimension at least 2n. It therefore fills the whole module.
No semisimplicity assumption is needed.

The small-offender SL₂(8) application uses this on its literal moved
central quotient. Source: Aschbacher--Smith E.2.13(4), p.225.
-/

public noncomputable section
open scoped MatrixGroups
namespace Representation.SL2
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- A module attaining the nontrivial minimum degree is irreducible if it
has no invariant vector. -/
theorem irreducible_of_fixed_free_minimal_binary_degree
    (ρ : Representation (ZMod 2) SL(2,F) V) [Nontrivial V]
    (hfix : ρ.invariants = ⊥) {n : ℕ} (hn : n ≠ 0)
    (hF : Nat.card F = 2 ^ n) (hd : Module.finrank (ZMod 2) V ≤ 2*n) :
    ρ.IsIrreducible := by
  obtain ⟨A,hA,_⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation ρ)).resolve_left top_ne_bot
  let : A.toRepresentation.IsIrreducible := (Subrepresentation.irreducible_iff_isAtom A).mpr hA
  have hnA : ∃ g, A.toRepresentation g ≠ 1 := by
    by_contra! hh
    have hb : A = ⊥ := by
      apply Subrepresentation.toSubmodule_injective
      apply bot_unique
      intro v hv
      apply hfix.le
      intro g
      exact congrArg Subtype.val (congrArg (fun f : Module.End (ZMod 2) A.toSubmodule =>
        f ⟨v,hv⟩) (hh g))
    exact hA.ne_bot hb
  have hlow := Unsigned.irreducible_finrank_bound 2 A.toRepresentation hnA n hn hF
  have htop : A = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.eq_top_of_finrank_eq
    have hu := Submodule.finrank_le A.toSubmodule
    omega
  exact isSimpleOrder_iff_isAtom_top.mpr (htop ▸ hA)

end Representation.SL2
