module

public import Theory.SpecificGroups.Lyons.Atlas111SimplicitySetup

/-!
# Simplicity reduction for the concrete Lyons matrix group

The certified involution identity and three further matrix word identities
give perfectness and normal generation by the first generator. If its
centralizer is maximal, a normal subgroup either lies
in the ambient center or equals the whole group. The local center bound below
eliminates the first possibility except for the trivial subgroup.

This is a conditional assembly theorem. Three word identities and the structure
of the actual matrix centralizer still require certificates; no unconditional
simplicity instance is asserted here. For the proposed local structure see
the `2.A11` maximal subgroup and involution centralizer in the ATLAS Lyons entry,
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Ly/ . The general proof is in
`Theory.GroupTheory.NormalGeneratorCentralizerSimplicity`.
-/

namespace Lyons

open SimplicityCertificate

/-- Actual matrix relations and local centralizer structure imply simplicity. -/
public theorem isSimpleGroup_of_relations_and_centralizer
    (hb5 : generatorB ^ 5 = 1)
    (hab14 : (generatorA * generatorB) ^ 14 = 1) (hw67 : perfectWord ^ 67 = 1)
    (hmax : IsCoatom generatorCentralizer)
    (hcenter : ∀ z : generatorCentralizer,
      z ∈ Subgroup.center generatorCentralizer →
      (z : LyonsGroup) = 1 ∨ (z : LyonsGroup) = generatorA) : IsSimpleGroup LyonsGroup := by
  let := isPerfect_of_relations hb5 hab14 hw67
  exact Subgroup.isSimpleGroup_of_normal_generator_centralizer
    (normal_eq_top_of_generatorA_mem hb5 hab14) hmax hcenter

end Lyons
