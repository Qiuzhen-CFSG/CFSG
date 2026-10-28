module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Generators

/-!
# Collection words for the Held local cores

These finite lists specify concrete identities, proved in `Relations0`,
`Relations1` and `Relations2`. No identity is assumed by these definitions.
Source: GLS3 Table 5.3p; discovery script in `Cores/source`.
-/

@[expose] public section
namespace Held.TwoLocalCandidates.Cores

/-- Product of a list of core generators. -/
def coreProduct (i : Fin 3) (w : List (Fin 7)) : subgroup i :=
  (w.map (coreGenerator i)).prod

/-- The proposed conjugation action of a local generator on a core generator. -/
def conjugateWord : Fin 3 → Fin 2 → Fin 7 → List (Fin 7)
  | 0, 0, 0 => [1]
  | 0, 0, 1 => [0]
  | 0, 0, 2 => [0, 1, 2]
  | 0, 0, 3 => [4]
  | 0, 0, 4 => [3]
  | 0, 0, 5 => [1, 2, 3, 4, 5]
  | 0, 0, 6 => []
  | 0, 1, 0 => [0]
  | 0, 1, 1 => [2]
  | 0, 1, 2 => [3]
  | 0, 1, 3 => [5]
  | 0, 1, 4 => [0, 3, 4]
  | 0, 1, 5 => [1, 3]
  | 0, 1, 6 => []
  | 1, 0, 0 => [1]
  | 1, 0, 1 => [0]
  | 1, 0, 2 => [3]
  | 1, 0, 3 => [2]
  | 1, 0, 4 => [0, 1, 2, 3, 4]
  | 1, 0, 5 => [1, 3, 4, 5]
  | 1, 0, 6 => []
  | 1, 1, 0 => [0]
  | 1, 1, 1 => [2]
  | 1, 1, 2 => [0, 1, 2, 3]
  | 1, 1, 3 => [4]
  | 1, 1, 4 => [5]
  | 1, 1, 5 => [0, 2, 3, 5]
  | 1, 1, 6 => []
  | 2, 0, 0 => [0]
  | 2, 0, 1 => [2]
  | 2, 0, 2 => [1, 2, 3]
  | 2, 0, 3 => [1]
  | 2, 0, 4 => [0, 2, 5]
  | 2, 0, 5 => [0, 1, 3, 5, 6]
  | 2, 0, 6 => [2, 4, 5]
  | 2, 1, 0 => [0]
  | 2, 1, 1 => [3]
  | 2, 1, 2 => [4]
  | 2, 1, 3 => [5]
  | 2, 1, 4 => [6]
  | 2, 1, 5 => [1]
  | 2, 1, 6 => [2]

/-- The possible central commutator factor for the extraspecial candidate. -/
def commutatorBit (i : Fin 3) (k j : Fin 7) : Bool :=
  i == 2 && (
    (k == 1 && j == 4) ||
    (k == 2 && j == 4) ||
    (k == 2 && j == 5) ||
    (k == 2 && j == 6) ||
    (k == 3 && j == 6) ||
    (k == 4 && j == 1) ||
    (k == 4 && j == 2) ||
    (k == 4 && j == 6) ||
    (k == 5 && j == 2) ||
    (k == 6 && j == 2) ||
    (k == 6 && j == 3) ||
    (k == 6 && j == 4))

end Held.TwoLocalCandidates.Cores
