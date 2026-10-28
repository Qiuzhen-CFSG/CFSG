module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.Data

/-!
# A normalizing generating sequence for the Held seed

Finite certificates for the exact eight Held seed words from `../Source/seed_words.json`.
Sources: ATLAS HeG1-p2058B0; GLS3 Table 5.3p. The external discovery and
generation scripts only propose data; all identities are checked by Lean.
-/

namespace Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.Seed

@[expose] public def pcGenerator : Fin 10 → He
  | 0 => (seedGenerator 0)⁻¹
  | 1 => (seedGenerator 5)⁻¹ * seedGenerator 0 * seedGenerator 5
  | 2 => (seedGenerator 1)⁻¹ * (seedGenerator 0)⁻¹
  | 3 => seedGenerator 2 * (seedGenerator 0)⁻¹
  | 4 => (seedGenerator 6)⁻¹
  | 5 => (seedGenerator 3)⁻¹ * (seedGenerator 3)⁻¹
  | 6 => seedGenerator 3 * (seedGenerator 0)⁻¹
  | 7 => (seedGenerator 5)⁻¹ * seedGenerator 3 * seedGenerator 5
  | 8 => (seedGenerator 4)⁻¹ * (seedGenerator 0)⁻¹
  | 9 => (seedGenerator 5)⁻¹

@[expose] public def pcProduct (w : List (Fin 10)) : He := (w.map pcGenerator).prod

@[expose] public def conjugateWord : Fin 10 → Fin 10 → List (Fin 10)
  | 1, 0 => [0]
  | 2, 0 => [0]
  | 2, 1 => [1]
  | 3, 0 => [1]
  | 3, 1 => [0]
  | 3, 2 => [2]
  | 4, 0 => [1]
  | 4, 1 => [0]
  | 4, 2 => [2]
  | 4, 3 => [3]
  | 5, 0 => [0]
  | 5, 1 => [1]
  | 5, 2 => [2]
  | 5, 3 => [3, 2]
  | 5, 4 => [4, 2]
  | 6, 0 => [2, 0]
  | 6, 1 => [2, 1]
  | 6, 2 => [2]
  | 6, 3 => [4]
  | 6, 4 => [3, 2]
  | 6, 5 => [5]
  | 7, 0 => [2, 1]
  | 7, 1 => [2, 0]
  | 7, 2 => [2]
  | 7, 3 => [4]
  | 7, 4 => [3, 2, 1, 0]
  | 7, 5 => [5]
  | 7, 6 => [6, 4, 3, 2, 1]
  | 8, 0 => [2, 0]
  | 8, 1 => [2, 1]
  | 8, 2 => [2]
  | 8, 3 => [3]
  | 8, 4 => [4, 2]
  | 8, 5 => [5]
  | 8, 6 => [6, 5]
  | 8, 7 => [7, 5, 1, 0]
  | 9, 0 => [1]
  | 9, 1 => [0]
  | 9, 2 => [2, 1, 0]
  | 9, 3 => [3, 1, 0]
  | 9, 4 => [4]
  | 9, 5 => [5, 4, 3, 1]
  | 9, 6 => [7, 1]
  | 9, 7 => [6, 0]
  | 9, 8 => [8, 7, 6, 5, 4, 3, 0]
  | _, _ => []

@[expose] public def originalWord : Fin 8 → List (Fin 10)
  | 0 => [0]
  | 1 => [2, 0]
  | 2 => [3, 0]
  | 3 => [6, 0]
  | 4 => [8, 0]
  | 5 => [9]
  | 6 => [4]
  | 7 => [7, 6, 5, 4, 0]

end Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.Seed
