module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.Representative

/-!
# A triangular generating sequence for the fixed Held subgroup

The ten words are the reverse of the candidate polycyclic sequence retained
in `TwoGroup/Source/pc.g`. Reversal makes the normalizing series ascending.
The conjugate words are proposed normal forms; `Relations` proves them in
the actual Held carrier. These definitions assert no permutation identity.
Source: ATLAS HeG1-p2058B0 and HeG1-max3W1; see `Calculations/Source`.
-/

namespace Held.LocalPairs.SylowGeometry.Calculations.TwoGroup

/-- Short words in the four published representative generators. -/
@[expose] public def pcGenerator : Fin 10 → He
  | 0 => (generator 2)⁻¹ * generator 1 * generator 0 * generator 1 * generator 2 * (generator 1)⁻¹ * (generator 0)⁻¹ * (generator 1)⁻¹
  | 1 => (generator 0)⁻¹
  | 2 => (generator 3)⁻¹ * (generator 3)⁻¹ * (generator 0)⁻¹
  | 3 => (generator 1)⁻¹ * (generator 0)⁻¹ * (generator 1)⁻¹
  | 4 => (generator 3)⁻¹ * generator 1 * generator 0 * generator 1 * generator 3
  | 5 => (generator 2)⁻¹ * (generator 3)⁻¹ * (generator 0)⁻¹ * generator 1 * generator 0 * generator 1 * (generator 3)⁻¹ * (generator 1)⁻¹ * (generator 0)⁻¹ * (generator 2)⁻¹ * (generator 1)⁻¹
  | 6 => (generator 1)⁻¹
  | 7 => (generator 3)⁻¹ * generator 1 * generator 3
  | 8 => (generator 2)⁻¹
  | 9 => generator 3

/-- An ordered product in the ascending generating sequence. -/
@[expose] public def pcProduct (w : List (Fin 10)) : He :=
  (w.map pcGenerator).prod

/-- Proposed triangular conjugation normal forms. Only entries `j < k` are used. -/
@[expose] public def conjugateWord : Fin 10 → Fin 10 → List (Fin 10)
  | 1, 0 => [0]
  | 2, 0 => [0]
  | 2, 1 => [1]
  | 3, 0 => [0]
  | 3, 1 => [1]
  | 3, 2 => [2, 0]
  | 4, 0 => [0]
  | 4, 1 => [1, 0]
  | 4, 2 => [2]
  | 4, 3 => [3]
  | 5, 0 => [0]
  | 5, 1 => [1]
  | 5, 2 => [2]
  | 5, 3 => [3, 0]
  | 5, 4 => [4]
  | 6, 0 => [0]
  | 6, 1 => [3]
  | 6, 2 => [5, 4, 2]
  | 6, 3 => [1]
  | 6, 4 => [5]
  | 6, 5 => [4]
  | 7, 0 => [0]
  | 7, 1 => [5, 3, 2, 0]
  | 7, 2 => [4]
  | 7, 3 => [5, 2, 1]
  | 7, 4 => [2]
  | 7, 5 => [5, 4, 2]
  | 7, 6 => [6]
  | 8, 0 => [0]
  | 8, 1 => [1]
  | 8, 2 => [2]
  | 8, 3 => [3, 0]
  | 8, 4 => [4]
  | 8, 5 => [5, 0]
  | 8, 6 => [6, 5, 4, 3, 1, 0]
  | 8, 7 => [7]
  | 9, 0 => [0]
  | 9, 1 => [2]
  | 9, 2 => [1]
  | 9, 3 => [4, 0]
  | 9, 4 => [3]
  | 9, 5 => [5, 2, 1, 0]
  | 9, 6 => [7, 5, 4, 3, 1, 0]
  | 9, 7 => [6]
  | 9, 8 => [8, 2, 1]
  | _, _ => []

end Held.LocalPairs.SylowGeometry.Calculations.TwoGroup
