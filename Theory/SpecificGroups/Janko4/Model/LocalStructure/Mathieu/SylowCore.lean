module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.Reduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.FixedCoordinates
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.Transport
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.FiniteBound

/-!
# Characteristicity of the literal max1 kernel in local Sylow subgroups

The literal elementary kernel has order 2048 and lies in every local Sylow
two-subgroup. For a normal elementary subgroup not contained in the kernel,
the checked finite row-action bound and its transport to the actual quotient
bound its order by 1024. Thus every automorphic image of the kernel equals
the kernel, proving characteristicity without further premises.

The counting deduction is in `SylowCore.Reduction`, the actual quotient and
kernel-action comparison in `SylowCore.Transport`, and the kernel-checked
finite inequality in `SylowCore.FiniteBound`.

Source context: Kleidman–Wilson, *The maximal subgroups of J₄* (1988),
pp.484–510; GLS3 Table 5.3i. The literal ATLAS words are documented in
`Cardinality.Subgroup`; characteristicity is proved by the action bound,
rather than inferred from the table's extension shape.
-/

public section

namespace Janko4.LocalStructure
open Cardinality

/-- The literal max1 kernel is characteristic in every local Sylow two-subgroup. -/
theorem localKernel_sylow_characteristic
    (P : Sylow 2 (max1Subgroup matrixA_mul_self matrixB_pow_four)) :
    ((localKernel matrixA_mul_self matrixB_pow_four).subgroupOf P.toSubgroup).Characteristic :=
  localKernel_sylow_characteristic_of_quotientCentralizerBound
    (SylowCore.quotientCentralizerBound_of_fixedBound SylowCore.normalElementaryFixedBound) P

end Janko4.LocalStructure
