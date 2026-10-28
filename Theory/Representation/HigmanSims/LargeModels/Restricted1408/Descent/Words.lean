module

public import Mathlib.Data.Fin.VecNotation

/-!
# Signed words for the ATLAS HS presentation

The thirteen words retain the order of HSG1-P1.M: ten defining relations,
followed by the three additional source relations R1, R2 and R3. We include
all thirteen as defining relations and do not need their claimed redundancy.
Letters 0, 1, 2, 3 mean a, b, inverse a, inverse b. Source commutators are
inverse a * inverse b * a * b, as in Magma. See `source/README.md`.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation

/-- The literal signed relators of the preserved ATLAS Magma file. -/
def relatorLetters : Fin 13 → List (Fin 4) :=
  ![[0, 0],
    [1, 1, 1, 1, 1],
    [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1],
    [2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1],
    [2, 3, 2, 3, 0, 1, 0, 1, 2, 3, 2, 3, 0, 1, 0, 1, 2, 3, 2, 3, 0, 1, 0, 1],
    [2, 3, 3, 0, 1, 1, 2, 3, 3, 0, 1, 1, 2, 3, 3, 0, 1, 1, 2, 3, 3, 0, 1, 1, 2, 3, 3, 0, 1, 1, 2, 3, 3, 0, 1, 1],
    [0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 3, 3, 0, 3, 0, 1, 1, 0, 1, 0, 1, 0, 3, 3, 0, 3, 3, 0, 3, 3, 0, 3, 3],
    [0, 1, 0, 1, 1, 0, 3, 3, 0, 3, 3, 0, 1, 1, 0, 3, 3, 0, 3, 3, 0, 1, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1, 0, 3, 0, 1, 1],
    [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 3, 3, 0, 3, 0, 3, 3],
    [0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 3, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 3, 3, 0, 1, 0, 1, 0, 3],
    [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 3],
    [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 0, 3, 3, 0, 1, 0, 3, 0, 1, 1]]

end Sporadic.LeechRelated.HS.AtlasPresentation
