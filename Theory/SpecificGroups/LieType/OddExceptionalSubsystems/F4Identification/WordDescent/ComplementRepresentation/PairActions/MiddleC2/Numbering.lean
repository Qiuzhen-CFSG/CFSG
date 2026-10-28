module

public import Mathlib.Data.Fin.VecNotation

/-!
# Numbering for the middle C2 finite lattice

Rows are integer coefficients in the numbered simple-root bases. Roots are
ordered lexicographically; Cartan coordinates precede root coordinates.
`FiniteLattice` uses indices 0--3 for F4 Cartan coordinates, followed by
`sourceRoots`; the ambient E6 numbering uses indices 0--5 followed by
`ambientRoots`. The complementary coordinates are differences at the smaller
member of each nontrivial diagram pair, listed in `antiRepresentatives`.

These are explicit coordinate conventions, not a theorem identifying the
finite operators with the actual Geck operators. That comparison is the
remaining input of `SourceComparison` and `ComplementComparison`.
The data and their derivation are supplied in `source/`.

Sources: `Exceptional.lean` for the literal Cartan matrices,
`IntegralGeckConstruction.lean` for the operator formula, and GLS3 §2.6.2.
-/

@[expose] public section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.MiddleC2.Numbering

def sourceRoots : Fin 48 → Fin 4 → ℤ :=
  ![![-2, -3, -4, -2],
    ![-1, -3, -4, -2],
    ![-1, -2, -4, -2],
    ![-1, -2, -3, -2],
    ![-1, -2, -3, -1],
    ![-1, -2, -2, -2],
    ![-1, -2, -2, -1],
    ![-1, -2, -2, 0],
    ![-1, -1, -2, -2],
    ![-1, -1, -2, -1],
    ![-1, -1, -2, 0],
    ![-1, -1, -1, -1],
    ![-1, -1, -1, 0],
    ![-1, -1, 0, 0],
    ![-1, 0, 0, 0],
    ![0, -1, -2, -2],
    ![0, -1, -2, -1],
    ![0, -1, -2, 0],
    ![0, -1, -1, -1],
    ![0, -1, -1, 0],
    ![0, -1, 0, 0],
    ![0, 0, -1, -1],
    ![0, 0, -1, 0],
    ![0, 0, 0, -1],
    ![0, 0, 0, 1],
    ![0, 0, 1, 0],
    ![0, 0, 1, 1],
    ![0, 1, 0, 0],
    ![0, 1, 1, 0],
    ![0, 1, 1, 1],
    ![0, 1, 2, 0],
    ![0, 1, 2, 1],
    ![0, 1, 2, 2],
    ![1, 0, 0, 0],
    ![1, 1, 0, 0],
    ![1, 1, 1, 0],
    ![1, 1, 1, 1],
    ![1, 1, 2, 0],
    ![1, 1, 2, 1],
    ![1, 1, 2, 2],
    ![1, 2, 2, 0],
    ![1, 2, 2, 1],
    ![1, 2, 2, 2],
    ![1, 2, 3, 1],
    ![1, 2, 3, 2],
    ![1, 2, 4, 2],
    ![1, 3, 4, 2],
    ![2, 3, 4, 2]]

def ambientRoots : Fin 72 → Fin 6 → ℤ :=
  ![![-1, -2, -3, -2, -2, -1],
    ![-1, -2, -3, -1, -2, -1],
    ![-1, -2, -2, -1, -2, -1],
    ![-1, -2, -2, -1, -1, -1],
    ![-1, -2, -2, -1, -1, 0],
    ![-1, -1, -2, -1, -2, -1],
    ![-1, -1, -2, -1, -1, -1],
    ![-1, -1, -2, -1, -1, 0],
    ![-1, -1, -1, -1, -1, -1],
    ![-1, -1, -1, -1, -1, 0],
    ![-1, -1, -1, -1, 0, 0],
    ![-1, -1, -1, 0, -1, -1],
    ![-1, -1, -1, 0, -1, 0],
    ![-1, -1, -1, 0, 0, 0],
    ![-1, -1, 0, 0, 0, 0],
    ![-1, 0, 0, 0, 0, 0],
    ![0, -1, -2, -1, -2, -1],
    ![0, -1, -2, -1, -1, -1],
    ![0, -1, -2, -1, -1, 0],
    ![0, -1, -1, -1, -1, -1],
    ![0, -1, -1, -1, -1, 0],
    ![0, -1, -1, -1, 0, 0],
    ![0, -1, -1, 0, -1, -1],
    ![0, -1, -1, 0, -1, 0],
    ![0, -1, -1, 0, 0, 0],
    ![0, -1, 0, 0, 0, 0],
    ![0, 0, -1, -1, -1, -1],
    ![0, 0, -1, -1, -1, 0],
    ![0, 0, -1, -1, 0, 0],
    ![0, 0, -1, 0, -1, -1],
    ![0, 0, -1, 0, -1, 0],
    ![0, 0, -1, 0, 0, 0],
    ![0, 0, 0, -1, 0, 0],
    ![0, 0, 0, 0, -1, -1],
    ![0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 1, 0, 0],
    ![0, 0, 1, 0, 0, 0],
    ![0, 0, 1, 0, 1, 0],
    ![0, 0, 1, 0, 1, 1],
    ![0, 0, 1, 1, 0, 0],
    ![0, 0, 1, 1, 1, 0],
    ![0, 0, 1, 1, 1, 1],
    ![0, 1, 0, 0, 0, 0],
    ![0, 1, 1, 0, 0, 0],
    ![0, 1, 1, 0, 1, 0],
    ![0, 1, 1, 0, 1, 1],
    ![0, 1, 1, 1, 0, 0],
    ![0, 1, 1, 1, 1, 0],
    ![0, 1, 1, 1, 1, 1],
    ![0, 1, 2, 1, 1, 0],
    ![0, 1, 2, 1, 1, 1],
    ![0, 1, 2, 1, 2, 1],
    ![1, 0, 0, 0, 0, 0],
    ![1, 1, 0, 0, 0, 0],
    ![1, 1, 1, 0, 0, 0],
    ![1, 1, 1, 0, 1, 0],
    ![1, 1, 1, 0, 1, 1],
    ![1, 1, 1, 1, 0, 0],
    ![1, 1, 1, 1, 1, 0],
    ![1, 1, 1, 1, 1, 1],
    ![1, 1, 2, 1, 1, 0],
    ![1, 1, 2, 1, 1, 1],
    ![1, 1, 2, 1, 2, 1],
    ![1, 2, 2, 1, 1, 0],
    ![1, 2, 2, 1, 1, 1],
    ![1, 2, 2, 1, 2, 1],
    ![1, 2, 3, 1, 2, 1],
    ![1, 2, 3, 2, 2, 1]]

def diagram : Fin 78 → Fin 78 :=
  ![5, 4, 2, 3, 1, 0, 6, 7, 8, 11, 22, 9, 12, 23, 14, 25, 32, 17, 28, 35, 39, 41, 10, 13, 24, 15, 26, 33, 18, 29, 36, 40, 16, 27, 34, 19, 30, 37, 38, 20, 31, 21, 62, 52, 63, 45, 46, 53, 64, 49, 56, 67, 43, 47, 54, 65, 50, 57, 68, 59, 70, 73, 42, 44, 48, 55, 66, 51, 58, 69, 60, 71, 74, 61, 72, 75, 76, 77]

def antiRepresentatives : Fin 26 → Fin 78 :=
  ![0, 1, 9, 10, 13, 15, 16, 18, 19, 20, 21, 27, 30, 31, 42, 43, 44, 47, 48, 50, 51, 55, 58, 60, 61, 72]

/-- Every ambient coordinate is fixed or belongs to one listed diagram pair. -/
theorem diagram_pairs : ∀ i : Fin 78,
    diagram i = i ∨ ∃ j : Fin 26,
      i = antiRepresentatives j ∨ i = diagram (antiRepresentatives j) := by decide +kernel

/-- Every listed representative is the smaller member of a nontrivial pair. -/
theorem representative_lt : ∀ j : Fin 26,
    antiRepresentatives j < diagram (antiRepresentatives j) := by decide +kernel

theorem diagram_involutive : Function.Involutive diagram := by
  change ∀ i : Fin 78, diagram (diagram i) = i
  decide +kernel

theorem antiRepresentatives_injective : Function.Injective antiRepresentatives := by
  change ∀ i j : Fin 26, antiRepresentatives i = antiRepresentatives j → i = j
  decide +kernel

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.MiddleC2.Numbering
