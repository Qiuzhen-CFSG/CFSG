module

public import Theory.Character.ModularBlock.CyclicThirteenData

/-!+# Ordinary rows on a self-centralizing subgroup of order thirteen

This interface separates the ordinary exceptional-character construction from
block identification. It records seven distinct actual irreducible characters,
their restrictions, and vanishing of every remaining character on the punctured
Sylow subgroup. It does not assert that such rows exist or assume block membership.

The nonzero values follow from the signs and period irrationality. The assembly
in `CyclicThirteenRows` identifies these rows with the principal congruence block.
Source: Alperin--Brauer--Gorenstein, III.8, printed pp.116--117, and the
exceptional-character argument underlying Brauer's cyclic-block theorem.
-/

public section
noncomputable section
namespace ModularBlock.CyclicThirteen
open PrimeBlockConstruction
variable {G : Type*} [Group G] [Finite G]

/-- Ordinary spectral data, prior to identification of the congruence block. -/
structure OrdinaryRows (d : PrimeCongruenceBlockData 13 G) (P : Sylow 13 G) where
  rows : Fin 7 ↪ d.I
  principal_row : rows 0 = d.principal
  sign : Fin 3 → ℤ
  sign_unit : ∀ j, sign j = 1 ∨ sign j = -1
  sign_zero : sign 0 = 1
  nonexceptional_value : ∀ (j : Fin 3) (u : P), u ≠ 1 →
    d.chi (rows (j.castAdd 4)) (ConjClasses.mk (u : G)) = (sign j : ℂ)
  exceptionalDegree : ℕ
  exceptional_degree : ∀ k : Fin 4,
    d.chi (rows (k.natAdd 3)) (ConjClasses.mk 1) = (exceptionalDegree : ℂ)
  exceptionalSign : ℤ
  exceptionalSign_unit : exceptionalSign = 1 ∨ exceptionalSign = -1
  generator : P
  generator_ne_one : generator ≠ 1
  root : ℂ
  root_primitive : IsPrimitiveRoot root 13
  periods : Fin 4 × Fin 3 ≃ Fin 12
  exceptional_value : ∀ k : Fin 4,
    d.chi (rows (k.natAdd 3)) (ConjClasses.mk (generator : G)) =
      -(exceptionalSign : ℂ) * ThirteenPeriods.period root periods k
  off_rows_vanish : ∀ i : d.I, i ∉ Set.range rows → ∀ u : P, u ≠ 1 →
    d.chi i (ConjClasses.mk (u : G)) = 0

/-- All seven selected rows are nonzero at the distinguished generator. -/
theorem OrdinaryRows.value_ne_zero {d : PrimeCongruenceBlockData 13 G}
    {P : Sylow 13 G} (s : OrdinaryRows d P) (j : Fin 7) :
    d.chi (s.rows j) (ConjClasses.mk (s.generator : G)) ≠ 0 := by
  induction j using Fin.addCases (m := 3) (n := 4) with
  | left j =>
    rw [s.nonexceptional_value j s.generator s.generator_ne_one]
    rcases s.sign_unit j with h | h <;> simp [h]
  | right k =>
    rw [s.exceptional_value]
    intro h
    exact ThirteenPeriods.signed_period_not_rational s.root_primitive s.periods k
      s.exceptionalSign s.exceptionalSign_unit ⟨0, by simpa using h⟩

end ModularBlock.CyclicThirteen
