module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Model
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Arithmetic

/-!
# Shared literal word catalogue for the reverse-norm columns

The 65 occurrences in the nine generators use 26 distinct literal words.
The indices below only share those words: `generatorWords_eq_catalogue` checks
all nine lists, preserving their order and multiplicity. No word reduction or
action identity is used.

Source: Presentation/source/discovery/complete-generators.json and
randomwords.json; see Columns/source/README.md for provenance and regeneration.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns

def words : Fin 26 → List (Fin 4) :=
  ![[0, 1, 0, 1, 1],
    [3, 1, 1, 1, 3, 1, 0, 3, 3, 1, 3, 3, 0, 3, 0, 0, 1, 3, 0, 3],
    [1, 1, 0, 3, 1, 3, 3, 0, 1, 0, 3, 1, 3, 3, 3, 0, 3, 0, 1, 3],
    [1, 1, 1, 1, 3, 0, 0, 3, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 0],
    [3, 1, 3, 1, 1, 0, 1, 3, 0, 0, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1],
    [0, 3, 3, 0, 0, 0, 0, 3, 1, 3, 1, 3, 3, 3, 0, 0, 1, 0, 1, 1],
    [1, 0, 3, 3, 1, 1, 1, 1, 1, 3, 1, 1, 0, 0, 1, 0, 1, 0, 3, 3],
    [1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 3, 3, 1, 1, 1, 0, 0, 1, 0],
    [3, 1, 1, 0, 0, 3, 3, 1, 1, 3, 0, 3, 0, 3, 1, 1, 0, 3, 0, 1],
    [3, 1, 0, 0, 0, 1, 3, 0, 3, 0, 3, 3, 0, 1, 3, 0, 3, 3, 1, 0],
    [1, 0, 0, 1, 1, 1, 1, 3, 3, 3, 0, 1, 3, 1, 0, 1, 0, 0, 0, 0],
    [0, 3, 1, 1, 0, 0, 1, 3, 1, 1, 1, 3, 3, 3, 0, 0, 1, 1, 0, 1],
    [0, 3, 1, 0, 0, 1, 1, 3, 3, 0, 1, 1, 3, 1, 3, 3, 1, 3, 3, 0],
    [1, 1, 3, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 3, 3],
    [3, 1, 1, 0, 3, 3, 3, 0, 1, 1, 3, 3, 0, 0, 3, 1, 1, 0, 0, 1],
    [1, 3, 0, 1, 1, 1, 1, 1, 3, 0, 1, 1, 3, 0, 3, 3, 1, 0, 1, 3],
    [3, 1, 3, 1, 1, 3, 3, 3, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 3, 0],
    [0, 3, 0, 3, 0, 3, 0, 0, 3, 0, 3, 0, 0, 3, 0, 1, 0, 0, 0, 3],
    [0, 3, 1, 0, 0, 0, 1, 3, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1],
    [0, 3, 0, 1, 0, 3, 0, 1, 3, 3, 3, 3, 1, 1, 1, 0, 1, 0, 3, 0],
    [1, 3, 1, 1, 3, 3, 1, 1, 3, 0, 1, 3, 3, 0, 0, 0, 0, 1, 1, 3],
    [0, 1, 3, 0, 1, 1, 1, 3, 1, 0, 0, 3, 3, 3, 3, 0, 1, 3, 3, 3],
    [0, 1, 0, 0, 3, 1, 0, 3, 0, 0, 0, 1, 3, 1, 1, 3, 3, 3, 3, 0],
    [1, 1, 0, 1, 3, 1, 0, 0, 1, 0, 1, 3, 1, 1, 1, 1, 1, 0, 1, 0],
    [0, 1, 0, 0, 3, 3, 3, 1, 3, 0, 3, 3, 3, 3, 0, 3, 1, 1, 1, 0],
    [0, 1, 0, 3, 1, 3, 3, 0, 3, 0, 1, 0, 3, 1, 3, 1, 3, 0, 3, 3]]

def indices : Fin 9 → List (Fin 26) :=
  ![[2, 4, 5, 9, 13, 19, 21, 22],
    [3, 5, 6, 13, 16, 18, 19, 21],
    [7, 8, 9, 19, 21, 23, 24, 25],
    [1, 11, 14, 15, 16, 18, 23, 25],
    [5, 11, 12, 13, 15, 17, 23, 25],
    [7, 9, 13, 16, 18, 20, 22, 23],
    [2, 5, 9, 10, 12, 14, 20, 23],
    [10, 12, 14, 16, 17, 19, 23, 24],
    [0]]

theorem generatorWords_eq_catalogue (k : Fin 9) :
    generatorWords k = (indices k).map words := by
  revert k
  decide +kernel

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns
