module

public import Theory.Mathieu.M22.Properties.OuterCentralizers.FixedPointFree.Representative

/-!
# Conjugating words for fixed-point-free M₂₂ design involutions

Every fixed-point-free involution among the 256 certified Sylow rows is
conjugate to row 24 by one of the following words in actual M₂₂ generators.
`row_cases` checks the identities by kernel reduction. The remaining rows
have a nonidentity square or a fixed point. The word discovery script is
`source/generate.py`; its output is not trusted without these checks.

Source: the fixed-point-free branch of Aschbacher–Smith 16.1.5(5), p.1171.
-/

@[expose] public section
namespace Sporadic.Mathieu.M22OuterCentralizers.FixedPointFree
open M22CubicInverters
set_option maxRecDepth 100000

/-- Actual M₂₂ words sending the marked involution to each relevant Sylow row. -/
def conjugatingWord : Fin 18 → List (Fin 3) :=
  ![
    [],
    [2,0,2,0,1,0,1,1,0,2],
    [1,1,0,2,0,1,0,1,0,1,0,2,0,2],
    [0,1,0,1,1,0,2,0,1,0,1,1,0],
    [1,0,2,0,2,0,1,0,2,0],
    [1,1,0,1,0,1,1,0,1,0,1,0,1,0,1],
    [1,1,0,2,0,1,1,0,2,0,1],
    [2,0,2,0,1,1,0,1,0],
    [1,1,0,1,0,1,1,0,2,0,2,0,2,0,1,1,0],
    [1,1,0,2,0,2,0,1,1,0,1,0],
    [1,1,0,1,0,1,0,2,0,1],
    [0,1,0,1,0,2,0,1,0,2],
    [1,0,2,0,1,1,0,1,0,1,0,2],
    [1,1,0,1,0,1,0,1,0,1,1,0,1],
    [1,0,1,1,0,2,0,2,0,2,0,1,1,0],
    [1,1,0,1,0,1,1,0,2,0,1],
    [2,0,2,0,1,0,1,1,0,1],
    [2,0,2,0,2,0,1,0,1,0,1]]

/-- Index of the conjugating word for a Sylow row; unused rows map to zero. -/
def conjugatingIndex (i : Fin 256) : Fin 18 :=
  match i.val with
  | 24 => 0
  | 43 => 1
  | 61 => 2
  | 79 => 3
  | 91 => 4
  | 93 => 5
  | 109 => 6
  | 111 => 7
  | 124 => 8
  | 138 => 9
  | 158 => 10
  | 174 => 11
  | 186 => 12
  | 201 => 13
  | 219 => 14
  | 223 => 15
  | 236 => 16
  | 249 => 17
  | _ => 0

/-- The exhaustive certificate uses only permutation squares and fixed points. -/
theorem row_cases (i : Fin 256) :
    (∃ x, rowTable i (rowTable i x) ≠ x) ∨
    (∃ x, rowTable i x = x) ∨
    (∀ x, rowTable i (innerWordAction (conjugatingWord (conjugatingIndex i)) x) =
      innerWordAction (conjugatingWord (conjugatingIndex i)) (representativeTable x)) := by
  revert i
  decide +kernel

end Sporadic.Mathieu.M22OuterCentralizers.FixedPointFree
