module

public import Theory.Character.ModularBlock.CyclicSevenData

/-!
# Ordinary rows on a self-centralizing subgroup of order seven

This interface separates the ordinary exceptional-character construction from
block identification. It records five distinct actual irreducible characters,
their restrictions, and vanishing of every remaining character on the punctured
Sylow subgroup. It does not assert that such rows exist or assume block membership.

The nonzero values follow from the signs and period irrationality. The assembly
in `CyclicSevenRows` identifies these rows with the principal congruence block.
Source: Fong (1967), printed p.75, citing Brauer (1942).
Adapted from the project's corresponding cyclic-thirteen module.
-/

public section
noncomputable section
namespace ModularBlock.CyclicSeven
open PrimeBlockConstruction
variable {G : Type*} [Group G] [Finite G]

/-- Ordinary spectral data, prior to identification of the congruence block. -/
structure OrdinaryRows (d : PrimeCongruenceBlockData 7 G) (P : Sylow 7 G) where
  rows : Fin 5 ↪ d.I
  principal_row : rows 0 = d.principal
  sign : Fin 2 → ℤ
  sign_unit : ∀ j, sign j = 1 ∨ sign j = -1
  sign_zero : sign 0 = 1
  nonexceptional_value : ∀ (j : Fin 2) (u : P), u ≠ 1 →
    d.chi (rows (j.castAdd 3)) (ConjClasses.mk (u : G)) = (sign j : ℂ)
  exceptionalDegree : ℕ
  exceptional_degree : ∀ k : Fin 3,
    d.chi (rows (k.natAdd 2)) (ConjClasses.mk 1) = (exceptionalDegree : ℂ)
  exceptionalSign : ℤ
  exceptionalSign_unit : exceptionalSign = 1 ∨ exceptionalSign = -1
  generator : P
  generator_ne_one : generator ≠ 1
  root : ℂ
  root_primitive : IsPrimitiveRoot root 7
  periods : Fin 3 × Fin 2 ≃ Fin 6
  exceptional_value : ∀ k : Fin 3,
    d.chi (rows (k.natAdd 2)) (ConjClasses.mk (generator : G)) =
      -(exceptionalSign : ℂ) * SevenPeriods.period root periods k
  off_rows_vanish : ∀ i : d.I, i ∉ Set.range rows → ∀ u : P, u ≠ 1 →
    d.chi i (ConjClasses.mk (u : G)) = 0

/-- All five selected rows are nonzero at the distinguished generator. -/
theorem OrdinaryRows.value_ne_zero {d : PrimeCongruenceBlockData 7 G}
    {P : Sylow 7 G} (s : OrdinaryRows d P) (j : Fin 5) :
    d.chi (s.rows j) (ConjClasses.mk (s.generator : G)) ≠ 0 := by
  induction j using Fin.addCases (m := 2) (n := 3) with
  | left j =>
    rw [s.nonexceptional_value j s.generator s.generator_ne_one]
    rcases s.sign_unit j with h | h <;> simp [h]
  | right k =>
    rw [s.exceptional_value]
    intro h
    exact SevenPeriods.signed_period_not_rational s.root_primitive s.periods k
      s.exceptionalSign s.exceptionalSign_unit ⟨0, by simpa using h⟩

end ModularBlock.CyclicSeven
