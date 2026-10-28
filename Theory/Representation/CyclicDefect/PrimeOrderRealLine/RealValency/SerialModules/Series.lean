module

public import Theory.Representation.SubspaceQuotient

/-!
# Exhaustive series of actual invariant subspaces

An exhaustive finite series enumerates every subrepresentation in increasing
order. Its factors are the literal successive quotient representations, not
labels for characters. Such a series makes the subrepresentation lattice a
chain and rules out any decomposition into two nonzero summands.

This is the series interface for the reduced serial modules in Feit,
*The Representation Theory of Finite Groups*, VII.2.20 and VII.2.23.
Simplicity of the factors is supplied by their equivalences with the simple
edge representations in the vertex-family interface.
-/

public section
noncomputable section

namespace Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    {ρ : Representation K G V}

/-- The smaller invariant subspace, viewed inside the larger one. -/
@[expose] def inside (U W : Subrepresentation ρ) : Subrepresentation W.toRepresentation where
  toSubmodule := U.toSubmodule.comap W.toSubmodule.subtype
  apply_mem_toSubmodule g _ hv := U.apply_mem_toSubmodule g hv

/-- An ascending finite enumeration of all invariant subspaces. There is no
existence instance: producing this order is the seriality theorem. -/
structure ExhaustiveSeries (ρ : Representation K G V) (s : ℕ) where
  term : Fin (s + 1) ≃o Subrepresentation ρ

namespace ExhaustiveSeries

variable {s : ℕ} (c : ExhaustiveSeries ρ s)

@[simp] theorem first : c.term 0 = ⊥ := c.term.map_bot

@[simp] theorem last : c.term (Fin.last s) = ⊤ := c.term.map_top

/-- The actual quotient of one term by its predecessor, with induced action. -/
@[expose] def factor (i : Fin s) :=
  (inside (c.term i.castSucc) (c.term i.succ)).quotientRepresentation

include c in
/-- Exhaustivity identifies seriality with a chain of invariant subspaces. -/
theorem total (U W : Subrepresentation ρ) : U ≤ W ∨ W ≤ U := by
  rcases le_total (c.term.symm U) (c.term.symm W) with h | h
  · exact Or.inl (by simpa using c.term.monotone h)
  · exact Or.inr (by simpa using c.term.monotone h)

include c in
/-- Two complementary invariant subspaces cannot both be nonzero. -/
theorem no_nontrivial_complement (U W : Subrepresentation ρ) (h : IsCompl U W) :
    U = ⊥ ∨ W = ⊥ := by
  rcases c.total U W with hUW | hWU
  · exact Or.inl (by simpa [inf_eq_left.mpr hUW] using h.inf_eq_bot)
  · exact Or.inr (by simpa [inf_eq_right.mpr hWU] using h.inf_eq_bot)

end ExhaustiveSeries
end Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules
