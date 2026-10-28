module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.ReflectionGeometry.Choice.Normalizer
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.ReflectionGeometry.Choice.Alternating
/-!
# Choosing Janko's actual reflection

The complement C = N(⟨w⟩) ∩ N(E) is identified, through the genuine E
quotient, with an order-eighteen normalizer in A6. In that normalizer every
element is either the identity, an inverting involution, or a product of two
inverting involutions. If all such involutions belonged to N(F), then C
would be contained in N(F), contradicting 18 ∤ 1920. Thus one of them is
the required reflection outside N(F). Its inversion identity is transported
through the marked quotient isomorphism, not inferred from its order.

This replaces the source's computation of N(B) ∩ N(F) by a divisibility
argument. The original global hypotheses remain in `exists_reflection`;
the stronger local theorem shows that they are unnecessary for this step.
The selected reflection is also applied to the actual Y construction.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 8, Lemma 17, p.16;
DOI 10.1016/0021-8693(68)90002-1.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
  (w : FusedNineIntersectionActor D k)
include L

/-- The actual common normalizer of E and ⟨w⟩ has order eighteen. -/
public theorem reflectionComplement_card : Nat.card (reflectionComplement D k w) = 18 := by
  obtain ⟨q, e, hq, _⟩ := exists_reflectionComplement_equiv D k w L
  exact (Nat.card_congr e.toEquiv).trans (ReflectionChoice.a6_three_normalizer q hq).1

/-- The genuine relative quotient N(B)/E has order eighteen. -/
public theorem normalizer_B_quotient_card :
    Nat.card (normalizer (B D k w : Set G) ⧸
      (CaseII.E D k).subgroupOf (normalizer (B D k w : Set G))) = 18 := by
  let : ((CaseII.E D k).subgroupOf (normalizer (B D k w : Set G))).Normal :=
    normal_subgroupOf_of_le_normalizer (normalizer_B_le_normalizer_E D k w)
  have hCN : reflectionComplement D k w ≤ normalizer (B D k w : Set G) := by
    rw [normalizer_B_eq_E_sup_reflectionComplement D k w]
    exact le_sup_right
  rw [Nat.card_congr (reflectionComplement_isComplement D k w).symm.QuotientMulEquiv.toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe hCN).toEquiv]
  exact reflectionComplement_card D k L w

/-- The source local normalizers already supply an inverting involution outside N(F). -/
public theorem exists_reflection_of_localAnalysis :
    ∃ z : G, orderOf z = 2 ∧ z ∈ normalizer (CaseII.E D k : Set G) ∧
      z ∈ normalizer (zpowers w.actor : Set G) ∧
      z ∉ normalizer (CaseII.F D k : Set G) ∧ z * w.actor * z⁻¹ = w.actor⁻¹ := by
  classical
  obtain ⟨q, e, hq, he⟩ := exists_reflectionComplement_equiv D k w L
  obtain ⟨_, t, ht2, hti, hcover⟩ := ReflectionChoice.a6_three_normalizer q hq
  let C := reflectionComplement D k w
  let a : C := ⟨w.actor, actor_mem_reflectionComplement D k w⟩
  have hEa : (e a : alternatingGroup (Fin 6)) = q := he
  have lift (c : C) (hc2 : orderOf (e c : alternatingGroup (Fin 6)) = 2)
      (hci : (e c : alternatingGroup (Fin 6)) * q * (e c : alternatingGroup (Fin 6))⁻¹ = q⁻¹) :
      orderOf (c : G) = 2 ∧ (c : G) * w.actor * (c : G)⁻¹ = w.actor⁻¹ := by
    refine ⟨by simpa only [orderOf_coe, MulEquiv.orderOf_eq] using hc2, ?_⟩
    have h : c * a * c⁻¹ = a⁻¹ := by
      apply e.injective
      apply Subtype.ext
      simpa only [map_mul, map_inv, coe_mul, coe_inv, hEa] using hci
    exact congrArg Subtype.val h
  have htN : t ∈ normalizer (zpowers q : Set (alternatingGroup (Fin 6))) :=
    (ReflectionChoice.normalizes_three_iff q t hq).mpr (Or.inr hti)
  let s : C := e.symm ⟨t, htN⟩
  have hs : (e s : alternatingGroup (Fin 6)) = t := congrArg Subtype.val (e.apply_symm_apply ⟨t, htN⟩)
  by_contra hnone
  have all (c : C) (hc2 : orderOf (e c : alternatingGroup (Fin 6)) = 2)
      (hci : (e c : alternatingGroup (Fin 6)) * q * (e c : alternatingGroup (Fin 6))⁻¹ = q⁻¹) :
      (c : G) ∈ normalizer (CaseII.F D k : Set G) := by
    by_contra hnot
    obtain ⟨hcorder, hcinv⟩ := lift c hc2 hci
    exact hnone ⟨c, hcorder, c.property.2, c.property.1, hnot, hcinv⟩
  have hsF : (s : G) ∈ normalizer (CaseII.F D k : Set G) :=
    all s (hs.symm ▸ ht2) (by rw [hs]; exact hti)
  have hCF : C ≤ normalizer (CaseII.F D k : Set G) := by
    intro c hc
    let cC : C := ⟨c, hc⟩
    rcases hcover (e cC) (e cC).property with hy1 | ⟨hy2, hyi⟩ | ⟨hy2, hyi⟩
    · have hc1 : cC = 1 := e.injective (Subtype.ext (by simpa using hy1))
      have heq : c = 1 := congrArg Subtype.val hc1
      exact heq ▸ (normalizer (CaseII.F D k : Set G)).one_mem
    · exact all cC hy2 hyi
    · have hprod : (s : G) * c ∈ normalizer (CaseII.F D k : Set G) := by
        apply all (s * cC)
        · simpa only [map_mul, coe_mul, hs] using hy2
        · simpa only [map_mul, coe_mul, hs] using hyi
      have hcF := (normalizer (CaseII.F D k : Set G)).mul_mem
        ((normalizer (CaseII.F D k : Set G)).inv_mem hsF) hprod
      simpa only [inv_mul_cancel_left] using hcF
  have hd := card_dvd_of_le hCF
  change Nat.card (reflectionComplement D k w) ∣ Nat.card (normalizer (CaseII.F D k : Set G)) at hd
  rw [reflectionComplement_card D k L w, normalizer_F_card D k L] at hd
  norm_num at hd

/-- Janko’s selected reflection, with all the ambient source inputs explicit. -/
public theorem exists_reflection [IsSimpleGroup G]
    (_hcard : Nat.card G = 443520)
    (_hN3 : ∀ P : Sylow 3 G, Nat.card (normalizer (P : Set G)) = 72)
    (_horders : ∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 11} : Finset ℕ)) :
    ∃ z : G, orderOf z = 2 ∧ z ∈ normalizer (CaseII.E D k : Set G) ∧
      z ∈ normalizer (zpowers w.actor : Set G) ∧
      z ∉ normalizer (CaseII.F D k : Set G) ∧ z * w.actor * z⁻¹ = w.actor⁻¹ :=
  exists_reflection_of_localAnalysis D k L w

/-- Applying the selected reflection to the literal Y construction gives order ninety-six. -/
public theorem exists_reflection_with_Y_card :
    ∃ z : G, orderOf z = 2 ∧ z ∈ normalizer (CaseII.E D k : Set G) ∧
      z ∈ normalizer (zpowers w.actor : Set G) ∧
      z ∉ normalizer (CaseII.F D k : Set G) ∧ z * w.actor * z⁻¹ = w.actor⁻¹ ∧
      Nat.card (Y D k w z) = 96 := by
  obtain ⟨z, hz2, hzE, hzQ, hzF, hzinv⟩ := exists_reflection_of_localAnalysis D k L w
  exact ⟨z, hz2, hzE, hzQ, hzF, hzinv, Y_card_of_reflection D k w z hz2 hzE hzQ hzF⟩

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
