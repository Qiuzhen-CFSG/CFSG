module

public import Theory.SpecificGroups.HaradaNorton.Order.LocalSubgroup

/-!
# A finite presentation certificate for the HN word subgroup

Suzuki's presentation (2.15) of `A₁₂` has ten generators. Generator zero
has cube one, the others have square one, adjacent products have cube one,
and the remaining relations are the root-product and commuting relations
below. A certificate must supply actual elements of the fixed word subgroup
and prove that they generate it; no identification is built into this data.

The sufficiency of these relations is proved in
`Theory.Alternating.Theorem523A6`. `Order.LocalCard` combines that theorem
with simplicity and the alternating-group order formula.
-/

namespace HaradaNorton.OrderCertificate

/-- Concrete witnesses for Suzuki's presentation of the local subgroup.
Every field is a proof obligation about the original matrix carrier. -/
public structure LocalSuzukiCertificate where
  gen : Fin 10 → localSubgroup
  root_cube : gen 0 ^ 3 = 1
  tail_square : ∀ i, i ≠ 0 → gen i ^ 2 = 1
  root_adjacent_cube : (gen 0 * gen 1) ^ 3 = 1
  tail_adjacent_cube : ∀ i : Fin 9, i ≠ 0 →
    (gen i.castSucc * gen i.succ) ^ 3 = 1
  root_far_square : ∀ j : Fin 10, 1 < j.val → (gen 0 * gen j) ^ 2 = 1
  tail_far_commute : ∀ i j : Fin 10, i ≠ 0 → j ≠ 0 →
    (i.val + 1 < j.val ∨ j.val + 1 < i.val) → Commute (gen i) (gen j)
  generates : Subgroup.closure (Set.range gen) = ⊤

end HaradaNorton.OrderCertificate
