module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Representatives
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Data
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Reduction
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Links.Propagation

/-!
# Residual Fi23 links from relator and seed certificates

The checked rank table reduces all residual connecting edges to eleven
short relator identities and eleven memberships in the unchanged closure
of `One0.permutation` and `One1.permutation`. The actual stabilizer consumer
below supplies this whole family to the existing Schreier reduction.

The identities and seed memberships remain outstanding. The loop hypotheses
are the independent contract of `First.Loops`; unconditional assembly remains
in `First.lean`. Source: ATLAS F23G1-p31671B0, GLS3 Table 5.3u and the Fischer
paragraph near line 1042 of `refs/KGroup/GLS3/Chapter5(sec3-).tex`.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection

namespace FirstTree

/-- A finite-certificate reduction with the literal residual-edge predicate. -/
theorem residual_a_edge_mem_of_relator_seed_certificates
    (hRelations : ∀ i : Fin 11, Links.wordValue (Links.relator i) = 1)
    (hSeeds : ∀ x : Fin 31671, Links.seed x = true → edge generatorA x ∈ KernelUpperData.first)
    (hAloops : ∀ x : Fin 31671, generatorA x = x → edge generatorA x ∈ KernelUpperData.first)
    (hBloops : ∀ x : Fin 31671, generatorB x = x → edge generatorB x ∈ KernelUpperData.first) :
    ∀ x : Fin 31671, x.val < (generatorA x).val → aTree x = false →
      edge generatorA x ∈ KernelUpperData.first := by
  intro x _ _
  exact Links.a_edges_of_rank_certificates hRelations hSeeds hAloops hBloops x

end FirstTree

open FirstTree

/-- The relator/seed route feeds the exact carrier-stabilizer reduction.
The two extra finite certificate premises are not yet discharged. -/
theorem first_stabilizer_le_of_relator_seed_certificates
    (hRelations : ∀ i : Fin 11, Links.wordValue (Links.relator i) = 1)
    (hSeeds : ∀ x : Fin 31671, Links.seed x = true → edge generatorA x ∈ KernelUpperData.first)
    (hAloops : ∀ x : Fin 31671, generatorA x = x → edge generatorA x ∈ KernelUpperData.first)
    (hBloops : ∀ x : Fin 31671, generatorB x = x → edge generatorB x ∈ KernelUpperData.first)
    (g : Carrier) (hg : inclusion g 1 = 1) : inclusion g ∈ KernelUpperData.first :=
  first_stabilizer_le_of_residual_edges hAloops hBloops
    (residual_a_edge_mem_of_relator_seed_certificates hRelations hSeeds hAloops hBloops) g hg

end Sporadic.Fischer.Fi23.CentralizerSection
