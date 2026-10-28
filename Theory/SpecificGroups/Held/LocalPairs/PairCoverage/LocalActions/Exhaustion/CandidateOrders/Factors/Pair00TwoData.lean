module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair00Two.P0
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair00Two.P1
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair00Two.P2
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair00Two.P3
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair00Two.P4
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair00Two.P5
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair00Two.P6
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair00Two.P7
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair00Two.P8
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair00Two.P9
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

def pcTable : Fin 10 → Equiv.Perm (Fin 2058)
  | 0 => p0
  | 1 => p1
  | 2 => p2
  | 3 => p3
  | 4 => p4
  | 5 => p5
  | 6 => p6
  | 7 => p7
  | 8 => p8
  | 9 => p9

theorem pcTable_eq (k : Fin 10) : pcTable k = representation (pc k) := by
  fin_cases k
  · exact p0_eq
  · exact p1_eq
  · exact p2_eq
  · exact p3_eq
  · exact p4_eq
  · exact p5_eq
  · exact p6_eq
  · exact p7_eq
  · exact p8_eq
  · exact p9_eq

end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors.Pair00Two
