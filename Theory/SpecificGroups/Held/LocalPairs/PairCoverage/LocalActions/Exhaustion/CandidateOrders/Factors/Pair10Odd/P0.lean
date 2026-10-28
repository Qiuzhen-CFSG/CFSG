module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair10OddWords
import Mathlib.Tactic.FinCases

/-!
# An explicit cyclic-series generator

The literal ATLAS degree-2058 action certifies every identity by kernel
reduction in bounded blocks. No numerical GAP output is a proof premise.
Sources: HeG1-p2058B0, max3/max4 programs, and LocalActions/source/Explore.g.
Reproduction: Factors/source/generate.py; proposed series: ../source/pcdata.json.
-/

set_option maxRecDepth 16384
set_option Elab.async false

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors.Pair10Odd
open Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate
open Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors

def p0 : Equiv.Perm (Fin 2058) := inputTable 1

theorem p0_eq : p0 = representation (pc 0) := by
  simp only [pc, map_evalSigned, ← inputTable_eq]
  simp [p0, evalSigned, pcWord]

end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors.Pair10Odd
