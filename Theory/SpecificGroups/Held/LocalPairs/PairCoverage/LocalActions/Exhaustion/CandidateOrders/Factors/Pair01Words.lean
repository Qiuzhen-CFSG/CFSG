module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Local0
import Mathlib.Tactic.FinCases

/-!
# The six unchanged candidate words

The literal ATLAS degree-2058 action certifies every identity by kernel
reduction in bounded blocks. No numerical GAP output is a proof premise.
Sources: HeG1-p2058B0, max3/max4 programs, and LocalActions/source/Explore.g.
Reproduction: Factors/source/generate.py; proposed series: ../source/pcdata.json.
-/

set_option maxRecDepth 16384
set_option Elab.async false

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors.Pair01
open Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate
open Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors

theorem map_local_word (w : List (Bool × ℤ)) :
    representation (evalLocalWord false w) =
      (w.map (fun t => (if t.1 then Local0.localTable else atlasA) ^ t.2)).prod := by
  simp only [evalLocalWord, map_list_prod, List.map_map, Function.comp_def,
    apply_ite representation, map_zpow, ← Local0.localTable_eq]
  rfl

def generator : Fin 6 → He
  | 0 => evalLocalWord false (oddWord false 1 0)
  | 1 => evalLocalWord false (oddWord false 1 1)
  | 2 => evalLocalWord false (twoWord false 1 0)
  | 3 => evalLocalWord false (twoWord false 1 1)
  | 4 => evalLocalWord false (twoWord false 1 2)
  | 5 => evalLocalWord false (twoWord false 1 3)


end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors.Pair01
