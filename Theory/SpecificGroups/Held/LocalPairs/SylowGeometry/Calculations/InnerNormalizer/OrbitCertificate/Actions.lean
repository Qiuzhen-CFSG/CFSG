module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.Representative
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.Data
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.OrbitCertificate.Tables
public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Tables0
import Mathlib.Tactic.FinCases

/-!
# Checked actions of the four Held representative generators

The local generators have previously checked packed permutation tables.
Transporting each signed word through the representation identifies evaluation
in these tables with the literal Held element. Kernel reduction then checks
all 2058 values of each of the four candidate action tables. Separate sequential
checks bound peak memory; the original signed words and their order are unchanged.

Source: `Calculations/Representative`, ATLAS HeG1-p2058B0 and HeG1-max3W1.
The candidate tables are reproduced by `OrbitCertificate/Source/generate.py`.
-/

namespace Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.OrbitCertificate
open Held.TwoLocalCandidates.Cores.Tables0

set_option Elab.async false

private def fastGenerator (i : Fin 4) : Equiv.Perm (Fin 2058) :=
  ((generatorWord i).map (fun k => if k.natAbs = 1 then p0 ^ k else
    p1 ^ (if k < 0 then (-1 : ℤ) else 1))).prod
private theorem fastGenerator_eq (i : Fin 4) : fastGenerator i = representation (generator i) := by
  have ha : p0 = representation a := p0_eq
  have hb : p1 = representation (PairCoverage.localWord false) := p1_eq
  unfold fastGenerator generator evalLocalWord
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  dsimp only [Function.comp_def]
  split <;> simp only [ha, hb, map_zpow]
set_option maxRecDepth 16384 in
private theorem action_checked0 : ∀ x : Fin 2058,
    fastGenerator 0 x = action 0 x := by decide +kernel

set_option maxRecDepth 16384 in
private theorem action_checked1 : ∀ x : Fin 2058,
    fastGenerator 1 x = action 1 x := by decide +kernel

set_option maxRecDepth 16384 in
private theorem action_checked2 : ∀ x : Fin 2058,
    fastGenerator 2 x = action 2 x := by decide +kernel

set_option maxRecDepth 16384 in
private theorem action_checked3 : ∀ x : Fin 2058,
    fastGenerator 3 x = action 3 x := by decide +kernel

/-- The packed action is the action of the actual published generator word. -/
public theorem action_eq (i : Fin 4) (x : Fin 2058) :
    action i x = representation (generator i) x := by
  rw [← fastGenerator_eq]
  fin_cases i
  · exact (action_checked0 x).symm
  · exact (action_checked1 x).symm
  · exact (action_checked2 x).symm
  · exact (action_checked3 x).symm

end Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.OrbitCertificate
