module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.Reduction
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.InitialSteps

/-!
# Third Fi23 prefix stabilizer containment: certificate assembly interface

`third_stabilizer_le_of_certificates` connects the checked representative and
inverse-transition data to the exact six source permutations and seven original
cycle-decoded target permutations. Unconditional containment still requires
`KernelUpperThird.Step` for all six indices and the seven generator comparisons.
Final assembly remains here; the conditional theorem is not the completed
third stabilizer theorem.

Source: ATLAS F23G1-p31671B0; GLS3 Table 5.3u.
-/
