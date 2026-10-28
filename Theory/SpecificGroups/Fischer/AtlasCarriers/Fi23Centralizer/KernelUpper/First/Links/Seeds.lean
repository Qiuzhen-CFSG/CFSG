module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Links.Seeds.Checks.Initial
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Links.Seeds.OutputBridge
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Links.Propagation

/-!
# Seed-program application to all first-stage Fi23 Schreier edges

This is the assembly interface for the fixed shared program: its local table
equations and its actual output comparisons supply the eleven seed memberships
to the existing rank induction. The relators and loop hypotheses are retained.
Until both finite equation families have proofs, this is only a conditional
application, not the desired loop-only membership theorem.

Source: ATLAS F23G1-p31671B0 and GLS3 Table 5.3u.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Links

theorem a_edges_of_seed_program_certificates
    (hsteps : ∀ k, 5 ≤ k → k < 345 → Seeds.Equation Seeds.table k (Seeds.program k))
    (houtputs : Seeds.OutputEquations)
    (hRelations : ∀ i : Fin 11, wordValue (relator i) = 1)
    (hAloops : ∀ x : Fin 31671, generatorA x = x → edge generatorA x ∈ KernelUpperData.first)
    (hBloops : ∀ x : Fin 31671, generatorB x = x → edge generatorB x ∈ KernelUpperData.first)
    (x : Fin 31671) : edge generatorA x ∈ KernelUpperData.first :=
  a_edges_of_rank_certificates hRelations
    (Seeds.seed_edges_mem_of_equations (Seeds.steps_of_remaining hsteps)
      (Seeds.outputs_of_word_equations houtputs))
    hAloops hBloops x

end Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Links
