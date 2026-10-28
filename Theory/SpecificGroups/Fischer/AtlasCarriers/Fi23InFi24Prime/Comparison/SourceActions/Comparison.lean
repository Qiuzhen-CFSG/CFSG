module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.SourceActions

/-!
# Applying the exact source-action certificates to the lift comparison

The two source-map premises of the orbit relabeling theorem are discharged by
the exact Fi23 generator certificates. Only the two ambient word intertwinings
remain explicit. Their assembly belongs to the unconditional lift comparison.

Source: GLS3 Table 5.3v; the literal ATLAS carriers, quotient-free orbit action,
and relabeling conventions are those of `Comparison`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift
open Certificate

/-- The source actions are certified; only the ambient word actions remain. -/
theorem exists_generator_comparison_of_ambient_certificates
    (hambientA : ∀ i, candidateA.val (labelMap i) = labelMap (sourceA i))
    (hambientB : ∀ i, candidateB.val (labelMap i) = labelMap (sourceB i)) :
    ∃ j : Fin 31671 ≃ Letters,
      action aLift = j.permCongrHom Fi23.generatorA ∧
      action bLift = j.permCongrHom Fi23.generatorB :=
  exists_generator_comparison_of_pointwise_certificates
    generatorA_apply_eq_sourceA generatorB_apply_eq_sourceB hambientA hambientB

end Sporadic.Fischer.Fi24Prime.Fi23Lift
