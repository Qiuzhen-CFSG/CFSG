module

public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Defs
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Reduction
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Factors
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Product

/-!
# Quaternion central products and strict residual enlargement

The embedded recognition interface retains the local cubic action, the original
quaternion factors, and their common center. The order reduction derives order
576 from the local S3 quotient, the shared Sylow subgroup and strict enlargement
of the two-residual, then constructs independent cubic actors on the factors.
Each quaternion factor extended by its independent actor is an actual SL₂(3)
subgroup with that quaternion two-core. The two extensions commute, intersect
in the original common center, and generate exactly the ambient two-residual.
The final theorem retains the specified local cubic and places it in this
product; its conjugation actions and the original embeddings are unchanged.

Source: Aschbacher–Smith, Lemma 14.2.21, printed p.988 (PDF p.1005).
Only the restricted residual-enlargement calculation in its proof is asserted
here, not the full amalgam classification or subsequent normalizer argument.
-/

namespace Subgroup

/-- Recognize the two specified independent cubic extensions, retaining their
ambient embeddings and identifying their join with the actual two-residual. -/
public theorem QuaternionIndependentCubics.residual_central_product
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] (d : QuaternionCentralProductData Q)
    (hG : Nat.card G = 576)
    (actors : QuaternionIndependentCubics (d.left.map Q.subtype) (d.right.map Q.subtype)) :
    ∃ c : QuaternionResidualCentralProduct Q d,
      c.left = d.left.map Q.subtype ⊔ zpowers (actors.x : G) ∧
      c.right = d.right.map Q.subtype ⊔ zpowers (actors.y : G) := by
  have hB : Nonempty (d.left.map Q.subtype ≃* QuaternionGroup 2) :=
    ⟨(d.left.equivMapOfInjective Q.subtype Q.subtype_injective).symm.trans
      d.left_model.some⟩
  have hC : Nonempty (d.right.map Q.subtype ≃* QuaternionGroup 2) :=
    ⟨(d.right.equivMapOfInjective Q.subtype Q.subtype_injective).symm.trans
      d.right_model.some⟩
  obtain ⟨hLmodel, hLcore⟩ := quaternion_cubic_extension_recognition
    (d.left.map Q.subtype) hB (actors.x : G) actors.x_order (actors.actionB actors.x)
    (actors.actionB_apply actors.x) actors.x_actionB_ne_one
  obtain ⟨hRmodel, hRcore⟩ := quaternion_cubic_extension_recognition
    (d.right.map Q.subtype) hC (actors.y : G) actors.y_order (actors.actionC actors.y)
    (actors.actionC_apply actors.y) actors.y_actionC_ne_one
  obtain ⟨_, _, hcomm, hinter, hspan⟩ := actors.extensions_product Q d hG
  exact ⟨{
    left := d.left.map Q.subtype ⊔ zpowers (actors.x : G)
    right := d.right.map Q.subtype ⊔ zpowers (actors.y : G)
    left_model := hLmodel
    right_model := hRmodel
    left_contains := le_sup_left
    right_contains := le_sup_left
    left_core := hLcore
    right_core := hRcore
    commute := hcomm
    intersection := hinter
    span := hspan }, rfl, rfl⟩

/-- Restricted residual enlargement in the quaternion-plus branch of 14.2.21.
The normal self-centralizing two-core, local S₃ quotient and shared ambient
Sylow subgroup force the two-residual to be an embedded central product of
SL₂(3)'s extending the original quaternion factors. The given local cubic,
with its specified nontrivial actions on both factors, belongs to that product.
No independent-actor, order-576 or recognition premise is left to discharge. -/
public theorem quaternion_residual_central_product_of_residual_enlargement
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] (d : QuaternionCentralProductData Q)
    (hcore : Q = pCore 2 G) (hcentral : centralizer (Q : Set G) ≤ Q)
    (H : Subgroup G) (hQH : Q ≤ H)
    (e : H ⧸ Q.subgroupOf H ≃* Equiv.Perm (Fin 3))
    (S : Sylow 2 G) (hSH : (S : Subgroup G) ≤ H)
    (cubic : QuaternionLocalCubic Q H d)
    (hstrict : (pResidual 2 H).map H.subtype < pResidual 2 G) :
    ∃ c : QuaternionResidualCentralProduct Q d,
      (cubic.element : G) ∈ c.left ⊔ c.right := by
  subst Q
  have hG := card_eq_576_of_quaternion_product_residual_enlargement
    (pCore 2 G) d hcentral H hQH e S hSH hstrict
  obtain ⟨actors⟩ := independent_cubics_of_normal_quaternion_product_card_576
    (pCore 2 G) d hcentral hG
  obtain ⟨c, _, _⟩ := actors.residual_central_product (pCore 2 G) d hG
  refine ⟨c, ?_⟩
  rw [c.span]
  exact mem_pResidual_of_orderOf_coprime (by rw [cubic.order]; decide)

end Subgroup
