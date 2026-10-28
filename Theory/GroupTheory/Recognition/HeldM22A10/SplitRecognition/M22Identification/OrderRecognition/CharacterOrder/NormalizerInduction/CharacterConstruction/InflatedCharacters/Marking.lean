module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.Quotient
public import Theory.GroupTheory.ElementaryTwoKernelFusion
public import Theory.GroupTheory.PrimeOrderLift

/-!
# Marking the quotient representatives for normalizer inflation

The actual quotient kills the binary factor, preserves the faithful S4 actors,
and preserves the orders of the odd-order representatives. Reflection of
order-three conjugacy through its exponent-two kernel shows that the two
marked order-three classes remain distinct in A6. The final formula computes
all twelve quotient images using the original centralizer coordinates.

Source: Janko, *A characterization of the Mathieu simple groups, I*, §6,
pp.10–11. These are the group-theoretic inputs for the seven inflated rows.
-/

open Subgroup
noncomputable section
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer)
    (K : Subgroup (normalizer (CaseII.E D k : Set G)))
    (hK : ((CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G))).IsComplement' K)
    (eK : K ≃* alternatingGroup (Fin 6))

local notation "π" => normalizerQuotient D k K hK eK

/-- Every element of the actual quotient kernel has square one. -/
public theorem normalizerQuotient_square_kernel (L : LocalAnalysisData D k)
    (x : normalizer (CaseII.E D k : Set G)) (hx : π x = 1) : x ^ 2 = 1 := by
  let := L.E_elementary
  have hxE : (x : G) ∈ CaseII.E D k := by
    change x ∈ (CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G))
    rw [← normalizerQuotient_ker D k K hK eK]
    exact hx
  apply Subtype.ext
  exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : G) hxE

/-- The quotient preserves the order of an odd-order element. -/
public theorem normalizerQuotient_orderOf_odd (L : LocalAnalysisData D k)
    (x : normalizer (CaseII.E D k : Set G)) (hx : Nat.Coprime 2 (orderOf x)) :
    orderOf (π x) = orderOf x := by
  have hp : IsPGroup 2 (π).ker := by
    intro y
    refine ⟨1, ?_⟩
    apply Subtype.ext
    exact normalizerQuotient_square_kernel D k K hK eK L y y.property
  exact (π).orderOf_map_eq_of_coprime_of_isPGroup_ker hp x hx

/-- The original S4 actors retain their orders in the quotient. -/
public theorem normalizerQuotient_actor_order (s : SymmetricFour) :
    orderOf (π (normalizerCentralizer D k (SemidirectProduct.inr s))) = orderOf s :=
  orderOf_injective ((π).comp (normalizerActor D k))
    (normalizerQuotient_actor_injective D k K hK eK) s

/-- The image of the marked actor a is an involution. -/
public theorem normalizerQuotient_a_order :
    orderOf (π (normalizerCentralizer D k CaseII.a)) = 2 := by
  rw [CaseII.a, normalizerQuotient_actor_order]
  apply orderOf_eq_prime <;> decide +kernel

/-- The image of the marked actor c has order three. -/
public theorem normalizerQuotient_c_order :
    orderOf (π (normalizerCentralizer D k CaseII.c)) = 3 := by
  rw [CaseII.c, normalizerQuotient_actor_order]
  apply orderOf_eq_prime <;> decide +kernel

/-- The image of the marked actor d is an involution. -/
public theorem normalizerQuotient_d_order :
    orderOf (π (normalizerCentralizer D k CaseII.d)) = 2 := by
  rw [CaseII.d, normalizerQuotient_actor_order]
  apply orderOf_eq_prime <;> decide +kernel

/-- The image of the marked actor bd has order four. -/
public theorem normalizerQuotient_bd_order :
    orderOf (π (normalizerCentralizer D k (CaseII.b * CaseII.d))) = 4 := by
  rw [CaseII.b, CaseII.d, ← map_mul, normalizerQuotient_actor_order]
  apply (orderOf_eq_iff (by decide : 0 < 4)).mpr
  constructor
  · decide +kernel
  · intro m hm hpos
    interval_cases m <;> decide +kernel

/-- The other marked order-three representative retains its order. -/
public theorem normalizerQuotient_otherThree_order (L : LocalAnalysisData D k)
    (Q : NormalizerClassData D k) : orderOf (π Q.otherThree) = 3 := by
  rw [normalizerQuotient_orderOf_odd D k K hK eK L _ (by rw [Q.otherThree_order]; decide),
    Q.otherThree_order]

/-- The marked order-five representative retains its order. -/
public theorem normalizerQuotient_five_order (L : LocalAnalysisData D k)
    (Q : NormalizerClassData D k) : orderOf (π Q.five) = 5 := by
  rw [normalizerQuotient_orderOf_odd D k K hK eK L _ (by rw [Q.five_order]; decide),
    Q.five_order]

/-- The two marked order-three classes remain distinct after quotienting. -/
public theorem normalizerQuotient_otherThree_not_isConj (L : LocalAnalysisData D k)
    (Q : NormalizerClassData D k) :
    ¬ IsConj (π Q.otherThree) (π (normalizerCentralizer D k CaseII.c)) := by
  intro h
  have hc : (normalizerCentralizer D k CaseII.c) ^ 3 = 1 := by
    rw [← map_pow, ← CaseII.actor_orders.2.2.1, pow_orderOf_eq_one, map_one]
  have h' := (π).isConj_of_map_isConj_of_cube_eq_one_of_square_kernel
    (normalizerQuotient_surjective D k K hK eK)
    (normalizerQuotient_square_kernel D k K hK eK L)
    (by rw [← Q.otherThree_order, pow_orderOf_eq_one]) hc h
  have heq : ConjClasses.mk (Q.representative 8) = ConjClasses.mk (Q.representative 7) :=
    ConjClasses.mk_eq_mk_iff_isConj.mpr h'
  have : (8 : Fin 12) = 7 := Q.distinct heq
  exact (by decide : (8 : Fin 12) ≠ 7) this

/-- The quotient kills each original basis vector. -/
public theorem normalizerQuotient_z (i : Fin 4) :
    π (normalizerCentralizer D k (CaseII.z i)) = 1 :=
  (normalizerQuotient_centralizer_eq_one_iff D k K hK eK _).mpr rfl

/-- All twelve marked images, including the five special representatives. -/
public theorem normalizerQuotient_representative (Q : NormalizerClassData D k) (r : Fin 12) :
    π (Q.representative r) =
      ![1, π (normalizerCentralizer D k CaseII.c),
        π (normalizerCentralizer D k (CaseII.b * CaseII.d)),
        π (normalizerCentralizer D k CaseII.a), π (normalizerCentralizer D k CaseII.d),
        1, π (normalizerCentralizer D k CaseII.a), π (normalizerCentralizer D k CaseII.c),
        π Q.otherThree, π (normalizerCentralizer D k (CaseII.b * CaseII.d)),
        π Q.five, (π Q.five) ^ 2] r := by
  have hz := normalizerQuotient_z D k K hK eK
  have hr (s) : normalizerRepresentative D k s =
      normalizerCentralizer D k (specialRepresentative s) := rfl
  fin_cases r <;>
    simp [NormalizerClassData.representative, normalizerFullRepresentative,
      normalizerNonspecialRepresentative, Fin.append, Fin.addCases, hr,
      specialRepresentative, map_mul, hz]

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
