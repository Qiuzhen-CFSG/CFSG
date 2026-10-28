module

public import Theory.GroupTheory.QuaternionCentralProductIntrinsic

/-!
# Transport of quaternion central-product presentations

A multiplicative equivalence transports the two embedded quaternion factors,
their intersection, their commutation, and their join. This preserves the
intrinsic Q₈ * Q₈ presentation used for concrete involution-centralizer kernels.

Source convention: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation E.2.16, printed p.228.
-/

namespace Subgroup.QuaternionCentralProductData

/-- Transport both embedded factors of the central product along an isomorphism. -/
public def map {G H : Type*} [Group G] [Group H]
    (d : QuaternionCentralProductData G) (e : G ≃* H) : QuaternionCentralProductData H where
  left := d.left.map e.toMonoidHom
  right := d.right.map e.toMonoidHom
  left_model := d.left_model.map fun f => (e.subgroupMap d.left).symm.trans f
  right_model := d.right_model.map fun f => (e.subgroupMap d.right).symm.trans f
  intersection_card := by
    rw [← Subgroup.map_inf _ _ _ e.injective,
      Subgroup.card_map_of_injective e.injective]
    exact d.intersection_card
  commute := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    change e b * e c = e c * e b
    simpa only [← map_mul] using congrArg e (d.commute b hb c hc)
  span := by
    rw [← Subgroup.map_sup, d.span, Subgroup.map_top_of_surjective _ e.surjective]

end Subgroup.QuaternionCentralProductData
