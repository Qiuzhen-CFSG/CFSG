module

public import Theory.GroupTheory.QuaternionCentralProductEnlargementOrder
public import Theory.GroupTheory.QuaternionCentralProductIndependentCubics
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Mathlib.Data.Fintype.Perm

/-!
# Order reduction for strict residual enlargement

The local S3 quotient and the intrinsic quaternion-product order give local
order 192. Strict residual enlargement forces this subgroup to be proper.
The shared ambient Sylow two-subgroup then gives order 576, by the existing
enlargement theorem. At that order the actual embedded quaternion factors
admit independent cubic actors.

Source: Aschbacher–Smith, Lemma 14.2.21, printed p.988 (PDF p.1005).
-/

namespace Subgroup

/-- The local S3 extension of the quaternion product has order 192. -/
public theorem card_eq_192_of_quaternion_product_quotient_s3 {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] (d : QuaternionCentralProductData Q)
    (H : Subgroup G) (hQH : Q ≤ H)
    (e : H ⧸ Q.subgroupOf H ≃* Equiv.Perm (Fin 3)) : Nat.card H = 192 := by
  have hQ : Nat.card (Q.subgroupOf H) = 32 :=
    (Nat.card_congr (subgroupOfEquivOfLe hQH).toEquiv).trans d.card
  have he : (Q.subgroupOf H).index = 6 := by
    rw [index_eq_card, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_perm, Fintype.card_fin]
    decide
  have hc := (Q.subgroupOf H).card_mul_index
  rw [hQ, he] at hc
  exact hc.symm


/-- Strict residual enlargement and a shared Sylow subgroup force order 576. -/
public theorem card_eq_576_of_quaternion_product_residual_enlargement {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] (d : QuaternionCentralProductData Q)
    (hcentral : centralizer (Q : Set G) ≤ Q)
    (H : Subgroup G) (hQH : Q ≤ H)
    (e : H ⧸ Q.subgroupOf H ≃* Equiv.Perm (Fin 3))
    (S : Sylow 2 G) (hSH : (S : Subgroup G) ≤ H)
    (hstrict : (pResidual 2 H).map H.subtype < pResidual 2 G) : Nat.card G = 576 := by
  exact card_eq_576_of_quaternion_product_enlargement Q d hcentral H
    (card_eq_192_of_quaternion_product_quotient_s3 Q d H hQH e) (ne_top_of_map_pResidual_lt 2 H hstrict) S hSH

/-- Construct independent actors on the original factors mapped into the ambient group. -/
public theorem independent_cubics_of_normal_quaternion_product_card_576 {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] (d : QuaternionCentralProductData Q)
    (hcentral : centralizer (Q : Set G) ≤ Q) (hG : Nat.card G = 576) :
    Nonempty (QuaternionIndependentCubics (d.left.map Q.subtype) (d.right.map Q.subtype)) := by
  have hj : d.left.map Q.subtype ⊔ d.right.map Q.subtype = Q := by
    rw [← Subgroup.map_sup, d.span]
    ext z
    exact ⟨fun ⟨w, _, hw⟩ => hw ▸ w.property, fun hz => ⟨⟨z, hz⟩, mem_top _, rfl⟩⟩
  apply exists_independent_cubics_of_quaternion_central_product
  · exact ⟨(d.left.equivMapOfInjective Q.subtype Q.subtype_injective).symm.trans d.left_model.some⟩
  · exact ⟨(d.right.equivMapOfInjective Q.subtype Q.subtype_injective).symm.trans d.right_model.some⟩
  · rw [← map_inf _ _ Q.subtype Q.subtype_injective,
      card_map_of_injective Q.subtype_injective, d.intersection_card]
  · rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    exact congrArg Subtype.val (d.commute b hb c hc)
  · rwa [hj]
  · rw [hj, Q.normalizer_eq_top, Nat.card_congr (topEquiv : (⊤ : Subgroup G) ≃* G).toEquiv]
    exact hG


end Subgroup
