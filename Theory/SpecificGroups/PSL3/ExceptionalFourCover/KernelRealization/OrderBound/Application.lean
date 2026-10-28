module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelRealization.OrderBound
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelRealization

/-!
# The concrete order certificate bounds the actual projective kernel

The checked upper bound discharges the order premise of
`kernel_card_le_of_order_bound` for the literal projection. Constructing the
central 48-element embedding and assembling the kernel equivalence remain
independent of this certificate.
Source: Aschbacher–Smith I.1.3(6), printed p.407; GLS3 §6.1.
-/

namespace Matrix.PSL3.ExceptionalFourCover.KernelModel

/-- The literal projection of the concrete realization has kernel of order at most 48. -/
public theorem kernel_card_le : Nat.card realizationProjection.ker ≤ 48 :=
  kernel_card_le_of_order_bound realization_card_le

end Matrix.PSL3.ExceptionalFourCover.KernelModel
