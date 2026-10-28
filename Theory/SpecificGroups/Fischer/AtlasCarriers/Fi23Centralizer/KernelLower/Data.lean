module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Data.AfterTwo
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.Data.AfterFour

/-!
# Shared endpoints of the Fi23 suffix stabilizer chain

`afterTwo` and `afterFour` are closures of literal permutations, not assumed
stabilizers. The independent transition certificates must connect these groups
to `KernelData.intermediate`. The checked fixed-point lemmas supply the target
subgroup's fixed-point hypotheses in the Schreier upper-bound theorem.
-/
