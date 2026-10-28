module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair01
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
namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors.Pair01Odd
open Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate
open Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors

def input : Fin 2 → He
  | 0 => Pair01.generator 0
  | 1 => Pair01.generator 1

def inputTable : Fin 2 → Equiv.Perm (Fin 2058)
  | 0 => Pair01.generatorTable 0
  | 1 => Pair01.generatorTable 1

theorem inputTable_eq (k : Fin 2) : inputTable k = representation (input k) := by
  fin_cases k
  · exact Pair01.generatorTable_eq 0
  · exact Pair01.generatorTable_eq 1

def pcWord : Fin 2 → List (Fin 2 × ℤ)
  | 0 => [(1, 1)]
  | 1 => [(0, 1)]

def pc (k : Fin 2) : He := evalSigned input (pcWord k)

def relativeOrder : Fin 2 → ℕ
  | 0 => 3
  | 1 => 3

def powerWord : Fin 2 → List (Fin 2)
  | 0 => []
  | 1 => []

def conjugateWord : Fin 2 → Fin 2 → List (Fin 2)
  | 0, 1 => [1]
  | _, _ => []

def inputWord : Fin 2 → List (Fin 2)
  | 0 => [1]
  | 1 => [0]

end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors.Pair01Odd
