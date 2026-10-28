module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Checks
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Contracts
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Reduction

/-!
# Finite action obligations for the first Fi23 fixed-point loops

Coverage and tree paths are checked. The shared subgroup words and the exact
Schreier action formula are interpreted in `Loops.Evaluation`. Two independent
numerical families and the shared-register comparison remain to be proved;
the reductions below consume precisely those obligations on the literal
carrier. They do not assert the unconditional loop-membership theorems.

Source: ATLAS F23G1-p31671B0 and GLS3 Table 5.3u.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops
open Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate

theorem a_fixed_edge_mem_of_actions (hc : CoreActions) (ha : AActions)
    (x : Fin 31671) (hx : generatorA x = x) :
    edge generatorA x ∈ KernelUpperData.first := by
  have h := (coverage x).1 (by simpa only [generatorA_apply_eq_sourceA] using hx)
  have hp := path_properties (loopIndex x)
  have hm := loop_edge_mem hc (loopIndex x) hp.1
    (by simpa only [sourceGenerator_eq] using hp.2) (ha _ h.1)
  simpa only [loopGenerator, if_pos h.1, h.2] using hm

theorem b_fixed_edge_mem_of_actions (hc : CoreActions) (hb : BActions)
    (x : Fin 31671) (hx : generatorB x = x) :
    edge generatorB x ∈ KernelUpperData.first := by
  have h := (coverage x).2 (by simpa only [generatorB_apply_eq_sourceB] using hx)
  have hp := path_properties (loopIndex x)
  have hm := loop_edge_mem hc (loopIndex x) hp.1
    (by simpa only [sourceGenerator_eq] using hp.2) (hb _ h.1)
  simpa only [loopGenerator, if_neg (not_lt.mpr h.1), h.2] using hm

/-- Concrete consumer of the three outstanding numerical certificates. Final
loop assembly must discharge all three; the residual links belong to the
independent first-step source branch. -/
theorem first_stabilizer_le_of_loop_actions (hc : CoreActions) (ha : AActions) (hb : BActions)
    (hlinks : ∀ x : Fin 31671, x.val < (generatorA x).val → aTree x = false →
      edge generatorA x ∈ KernelUpperData.first)
    (g : Carrier) (hg : inclusion g 1 = 1) : inclusion g ∈ KernelUpperData.first :=
  first_stabilizer_le_of_residual_edges
    (a_fixed_edge_mem_of_actions hc ha) (b_fixed_edge_mem_of_actions hc hb) hlinks g hg

end Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops
