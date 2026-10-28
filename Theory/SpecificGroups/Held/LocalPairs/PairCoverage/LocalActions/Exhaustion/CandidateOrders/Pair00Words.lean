module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Local0
import Mathlib.Tactic.FinCases

/-!
# Literal word generators for the first Held candidate pair

The six entries are exactly the two odd and four even generators already
published in `Candidates`. The representation formula uses the certified
max3 generator table. No order or collection identity is asserted here.
Sources: ATLAS HeG1-p2058B0/max3W1 and LocalActions/source/Explore.g.
-/

set_option maxRecDepth 16384
set_option Elab.async false

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Pair00
open Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate

theorem map_local_word (w : List (Bool × ℤ)) :
    representation (evalLocalWord false w) =
      (w.map (fun t => (if t.1 then Local0.localTable else atlasA) ^ t.2)).prod := by
  simp only [evalLocalWord, map_list_prod, List.map_map, Function.comp_def,
    apply_ite representation, map_zpow, ← Local0.localTable_eq]
  rfl

def generator : Fin 6 → He
  | 0 => evalLocalWord false (oddWord false 0 0)
  | 1 => evalLocalWord false (oddWord false 0 1)
  | 2 => evalLocalWord false (twoWord false 0 0)
  | 3 => evalLocalWord false (twoWord false 0 1)
  | 4 => evalLocalWord false (twoWord false 0 2)
  | 5 => evalLocalWord false (twoWord false 0 3)

end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Pair00
