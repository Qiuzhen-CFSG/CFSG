module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair00
import Mathlib.Tactic.FinCases

/-!
# Cyclic-series data for a Held candidate

The cyclic series consists of explicit words in the literal candidate generators.
The proposed data comes from the unchanged ATLAS degree-2058 carrier and
LocalActions/Candidates.lean. The Lean kernel checks every used identity.
See source/generate.py for reproduction; GAP output is not a premise.
-/

set_option maxRecDepth 16384
set_option Elab.async false

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors.Pair00Two
open Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate
open Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors

def input : Fin 4 → He
  | 0 => Pair00.generator 2
  | 1 => Pair00.generator 3
  | 2 => Pair00.generator 4
  | 3 => Pair00.generator 5

def inputTable : Fin 4 → Equiv.Perm (Fin 2058)
  | 0 => Pair00.generatorTable 2
  | 1 => Pair00.generatorTable 3
  | 2 => Pair00.generatorTable 4
  | 3 => Pair00.generatorTable 5

theorem inputTable_eq (k : Fin 4) : inputTable k = representation (input k) := by
  fin_cases k
  · exact Pair00.generatorTable_eq 2
  · exact Pair00.generatorTable_eq 3
  · exact Pair00.generatorTable_eq 4
  · exact Pair00.generatorTable_eq 5

def pcWord : Fin 10 → List (Fin 4 × ℤ)
  | 0 => [(1, 1), (3, 1), (1, 1), (0, 1)]
  | 1 => [(3, 1), (2, 1), (1, 1), (3, 1), (2, 1), (3, 1), (1, 1), (3, 1)]
  | 2 => [(2, 1)]
  | 3 => [(2, 1), (3, 1), (1, 1), (3, 1), (2, 1)]
  | 4 => [(3, 1), (1, 1), (3, 1)]
  | 5 => [(1, 1)]
  | 6 => [(1, 1), (3, 1), (2, 1), (0, 1), (2, 1), (3, 1), (1, 1), (0, 1)]
  | 7 => [(3, 1), (2, 1), (0, 1), (2, 1), (3, 1)]
  | 8 => [(2, 1), (0, 1), (2, 1), (0, 1)]
  | 9 => [(0, 1)]

def pc (k : Fin 10) : He := evalSigned input (pcWord k)

def relativeOrder : Fin 10 → ℕ
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | 7 => 2
  | 8 => 2
  | 9 => 2

def powerWord : Fin 10 → List (Fin 10)
  | 0 => []
  | 1 => []
  | 2 => []
  | 3 => []
  | 4 => []
  | 5 => []
  | 6 => []
  | 7 => []
  | 8 => []
  | 9 => []

def conjugateWord : Fin 10 → Fin 10 → List (Fin 10)
  | 0, 1 => [1]
  | 0, 2 => [1, 2, 7, 8, 9]
  | 0, 3 => [3, 4, 5, 6, 8]
  | 0, 4 => [5]
  | 0, 5 => [4]
  | 0, 6 => [8]
  | 0, 7 => [6, 7, 8]
  | 0, 8 => [6]
  | 0, 9 => [9]
  | 1, 2 => [2]
  | 1, 3 => [4, 7, 9]
  | 1, 4 => [3, 7, 9]
  | 1, 5 => [3, 4, 5, 7, 9]
  | 1, 6 => [6]
  | 1, 7 => [6, 7, 8]
  | 1, 8 => [8]
  | 1, 9 => [6, 8, 9]
  | 2, 3 => [4]
  | 2, 4 => [3]
  | 2, 5 => [5, 8]
  | 2, 6 => [6]
  | 2, 7 => [7, 8]
  | 2, 8 => [8]
  | 2, 9 => [8, 9]
  | 3, 4 => [4]
  | 3, 5 => [5, 6, 7, 9]
  | 3, 6 => [6]
  | 3, 7 => [6, 9]
  | 3, 8 => [6, 7, 8, 9]
  | 3, 9 => [6, 7]
  | 4, 5 => [5]
  | 4, 6 => [6]
  | 4, 7 => [7]
  | 4, 8 => [6, 7, 8, 9]
  | 4, 9 => [9]
  | 5, 6 => [7, 9]
  | 5, 7 => [6, 9]
  | 5, 8 => [8]
  | 5, 9 => [9]
  | 6, 7 => [7]
  | 6, 8 => [8]
  | 6, 9 => [9]
  | 7, 8 => [8]
  | 7, 9 => [9]
  | 8, 9 => [9]
  | _, _ => []

def inputWord : Fin 4 → List (Fin 10)
  | 0 => [9]
  | 1 => [5]
  | 2 => [2]
  | 3 => [0, 4, 5, 9]

end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors.Pair00Two
