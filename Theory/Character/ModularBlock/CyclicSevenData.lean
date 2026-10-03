module

public import Theory.Character.ModularBlock.PrimeCongruence
public import Theory.Character.SevenPeriods
public import Mathlib.GroupTheory.Sylow

/-!
# Spectral data for a cyclic block of order seven

This interface records the character-theoretic output of the cyclic-defect
row construction: two signed constant rows and three equal-degree rows
whose values at a generator are signed periods. The period indexing is a
partition of the six nontrivial roots into pairs. It carries neither
a rational-row criterion nor a signed degree equation; those follow from
period irrationality and block orthogonality in `CyclicSevenStructure`.

Source: Fong (1967), printed p.75, citing Brauer (1942).
Adapted from the project's corresponding cyclic-thirteen module.
-/

public section
noncomputable section
namespace ModularBlock.CyclicSeven
open PrimeBlockConstruction
variable {G : Type*} [Group G] [Finite G]

/-- The spectral output to be constructed from the cyclic Sylow hypotheses. -/
structure SpectralRows (d : PrimeCongruenceBlockData 7 G) (P : Sylow 7 G) where
  rows : Fin 5 ≃ {i : d.I // i ∈ d.block}
  principal_row : (rows 0).val = d.principal
  sign : Fin 2 → ℤ
  sign_unit : ∀ j, sign j = 1 ∨ sign j = -1
  sign_zero : sign 0 = 1
  nonexceptional_value : ∀ (j : Fin 2) (u : P), u ≠ 1 →
    d.chi (rows (j.castAdd 3)).val (ConjClasses.mk (u : G)) = (sign j : ℂ)
  exceptionalDegree : ℕ
  exceptional_degree : ∀ k : Fin 3,
    d.chi (rows (k.natAdd 2)).val (ConjClasses.mk 1) = (exceptionalDegree : ℂ)
  exceptionalSign : ℤ
  exceptionalSign_unit : exceptionalSign = 1 ∨ exceptionalSign = -1
  generator : P
  generator_ne_one : generator ≠ 1
  root : ℂ
  root_primitive : IsPrimitiveRoot root 7
  periods : Fin 3 × Fin 2 ≃ Fin 6
  exceptional_value : ∀ k : Fin 3,
    d.chi (rows (k.natAdd 2)).val (ConjClasses.mk (generator : G)) =
      -(exceptionalSign : ℂ) * SevenPeriods.period root periods k

end ModularBlock.CyclicSeven
