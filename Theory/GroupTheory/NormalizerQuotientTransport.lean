module
public import Mathlib.GroupTheory.Index

/-!
# Normalizer quotient cardinality under an ambient isomorphism

The normalizer maps onto the normalizer of the image subgroup. The order
of its literal quotient is the relative index, which an injective map
preserves. No finiteness or normality hypotheses need to be added.

This is used to transport the elementary-subgroup normalizer orders in
Aschbacher--Smith F.5.5, printed p.302.
-/

namespace Subgroup
variable {G H : Type*} [Group G] [Group H]
/-- An ambient isomorphism preserves the order of the literal normalizer quotient. -/
public theorem normalizer_quotient_card_map_equiv (e : G ≃* H) (B : Subgroup G) :
    Nat.card (normalizer (B.map e.toMonoidHom : Set H) ⧸
      (B.map e.toMonoidHom).subgroupOf (normalizer (B.map e.toMonoidHom : Set H))) =
    Nat.card (normalizer (B : Set G) ⧸ B.subgroupOf (normalizer (B : Set G))) := by
  rw [←index_eq_card,←index_eq_card]
  change (B.map e.toMonoidHom).relIndex (normalizer (B.map e.toMonoidHom : Set H)) =
    B.relIndex (normalizer (B : Set G))
  rw [←map_equiv_normalizer_eq,relIndex_map_map_of_injective _ _ e.injective]
end Subgroup
