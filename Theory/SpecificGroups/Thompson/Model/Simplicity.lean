module

public import Theory.SpecificGroups.Thompson.Model.Simplicity.Reduction
public import Theory.SpecificGroups.Thompson.Model.Simplicity.PrimeRepresentatives
public import Theory.SpecificGroups.Thompson.Model.Simplicity.NormalGenerationHigh

/-!
# Thompson matrix-model simplicity

The normal-subgroup reduction and normal-generation consequences of source
relations live in `Simplicity.Reduction`. `Simplicity.NormalGenerationHigh`
proves normal generation by representatives five through eight, conditional on
the standard product relation. Concrete prime-class coverage and the remaining
normal-generation certificates are required before this module can export the
simple-group instance for the fixed matrix carrier.
-/
