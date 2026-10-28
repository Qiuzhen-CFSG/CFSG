module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelRealization.OrderBound.Encoding
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelRealization.OrderBound.Tail

/-!
# Order upper bound for the literal exceptional PSL₃(4) extension

The actual subgroup of `Sym(224) × Sym(224) × SL₃(F₄)` embeds in a product
of transformation monoids. Five kernel-checked finite covers, with factors
224, 90, 4, 4, 3, bound the generated monoid by 967680. The initial two
transformations are checked against both literal permutations and the actual
column-vector matrix action. No numerical GAP order is a proof premise.

This certificate is independent of the central embedding and of the upper
bound on the universal covering group. Its application to the literal
projective kernel is in `OrderBound.Application` to avoid an import cycle.
Source: Aschbacher–Smith I.1.3(6), printed p.407; GLS3 §6.1.
-/

namespace Matrix.PSL3.ExceptionalFourCover.KernelModel

open OrderCertificate

/-- The concrete two-generated permutation/matrix model has at most 967680 elements. -/
public theorem realization_card_le : Nat.card Group ≤ 967680 := by
  exact (realization_card_le_of_encoded (Submonoid.closure (Set.range gen0))
    (by rw [encode_x]; exact Submonoid.subset_closure ⟨0, rfl⟩)
    (by rw [encode_y]; exact Submonoid.subset_closure ⟨1, rfl⟩)).trans encoded_card_le

end Matrix.PSL3.ExceptionalFourCover.KernelModel
