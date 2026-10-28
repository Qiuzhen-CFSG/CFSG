module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair01Odd.P0
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair01Odd.P1
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

def pcTable : Fin 2 → Equiv.Perm (Fin 2058)
  | 0 => p0
  | 1 => p1

theorem pcTable_eq (k : Fin 2) : pcTable k = representation (pc k) := by
  fin_cases k
  · exact p0_eq
  · exact p1_eq

end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors.Pair01Odd
