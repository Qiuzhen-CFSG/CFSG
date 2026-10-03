module

public import Theory.Character.ModularBlock.PrimeCongruence
public import Theory.Character.ThirteenPeriods
public import Mathlib.GroupTheory.Sylow

/-!
# Spectral data for a cyclic block of order thirteen

This interface records the character-theoretic output of the cyclic-defect
row construction: three signed constant rows and four equal-degree rows
whose values at a generator are signed periods. The period indexing is a
partition of the twelve nontrivial roots into triples. It carries neither
a rational-row criterion nor a signed degree equation; those follow from
period irrationality and block orthogonality in `CyclicThirteenStructure`.

Source: Alperin--Brauer--Gorenstein, III.8, printed pp.116--117, citing
Brauer's cyclic-block theorem [4], Theorem 11. This is a data interface,
not an assertion that the row construction exists.
-/

public section
noncomputable section
namespace ModularBlock.CyclicThirteen
open PrimeBlockConstruction
variable {G : Type*} [Group G] [Finite G]

/-- The spectral output to be constructed from the cyclic Sylow hypotheses. -/
structure SpectralRows (d : PrimeCongruenceBlockData 13 G) (P : Sylow 13 G) where
  rows : Fin 7 ≃ {i : d.I // i ∈ d.block}
  principal_row : (rows 0).val = d.principal
  sign : Fin 3 → ℤ
  sign_unit : ∀ j, sign j = 1 ∨ sign j = -1
  sign_zero : sign 0 = 1
  nonexceptional_value : ∀ (j : Fin 3) (u : P), u ≠ 1 →
    d.chi (rows (j.castAdd 4)).val (ConjClasses.mk (u : G)) = (sign j : ℂ)
  exceptionalDegree : ℕ
  exceptional_degree : ∀ k : Fin 4,
    d.chi (rows (k.natAdd 3)).val (ConjClasses.mk 1) = (exceptionalDegree : ℂ)
  exceptionalSign : ℤ
  exceptionalSign_unit : exceptionalSign = 1 ∨ exceptionalSign = -1
  generator : P
  generator_ne_one : generator ≠ 1
  root : ℂ
  root_primitive : IsPrimitiveRoot root 13
  periods : Fin 4 × Fin 3 ≃ Fin 12
  exceptional_value : ∀ k : Fin 4,
    d.chi (rows (k.natAdd 3)).val (ConjClasses.mk (generator : G)) =
      -(exceptionalSign : ℂ) * ThirteenPeriods.period root periods k

end ModularBlock.CyclicThirteen
