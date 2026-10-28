module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.BCensus
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.DerivedNormalizer
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion.IntersectionConstruction.LocalGeometry

/-!
# Consequences of Janko's normalizing involution

For any involution z normalizing E and the actual common order-three subgroup,
z normalizes B = E⟨w⟩. If z lies outside N(F), adjoining it doubles |B| to 96,
and Y ∩ X = B. These results use the literal generated subgroups and need no
assumption about the properness or index of their join.

The subgroup X ∩ Xᶻ contains B and is normalized by z. The involution preserves
neither E ∩ F nor EF: preserving either, together with E, would force it to
preserve F. These are the reductions used in the remaining intermediate-subgroup
classification. Existence of z and the reverse intersection containment are
not asserted in this module; neither is the remaining Y order census.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 8, Lemma 17, pp.16--17;
DOI 10.1016/0021-8693(68)90002-1.
-/

open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer) (w : FusedNineIntersectionActor D k)

omit [Finite G] in
/-- Normalizing the two generating subgroups normalizes their actual join. -/
public theorem normalizes_B_of_normalizes_E_and_actor (z : G)
    (hzE : z ∈ normalizer (CaseII.E D k : Set G))
    (hzQ : z ∈ normalizer (zpowers w.actor : Set G)) :
    z ∈ normalizer (B D k w : Set G) :=
  normalizer_inf_normalizer_le_normalizer_sup _ _ ⟨hzE, hzQ⟩

/-- The source normalizing involution gives the actual subgroup Y order 96. -/
public theorem Y_card_of_reflection (z : G) (hz2 : orderOf z = 2)
    (hzE : z ∈ normalizer (CaseII.E D k : Set G))
    (hzQ : z ∈ normalizer (zpowers w.actor : Set G))
    (hzF : z ∉ normalizer (CaseII.F D k : Set G)) : Nat.card (Y D k w z) = 96 := by
  rw [Y, card_sup_zpowers_of_normalizing_involution (B D k w) z
    (hz2 ▸ pow_orderOf_eq_one z)
    (fun hzB => hzF (B_le_normalizer_F D k w hzB))
    (normalizes_B_of_normalizes_E_and_actor D k w z hzE hzQ), B_card]

/-- The subgroup B lies in the intersection with the left conjugate of X. -/
public theorem B_le_conjugate_intersection (L : LocalAnalysisData D k) (z : G)
    (hzE : z ∈ normalizer (CaseII.E D k : Set G))
    (hzQ : z ∈ normalizer (zpowers w.actor : Set G)) :
    B D k w ≤ X D k ⊓ (X D k).map (MulAut.conj z).toMonoidHom := by
  refine le_inf (B_le_X D k L w) ?_
  have hB := mem_normalizer_iff_map_conj_eq.mp
    (normalizes_B_of_normalizes_E_and_actor D k w z hzE hzQ)
  exact hB.symm.le.trans (map_mono (B_le_X D k L w))

omit [Finite G] in
/-- An involution interchanges X with its conjugate, hence preserves their intersection. -/
public theorem reflection_normalizes_conjugate_intersection (z : G) (hz2 : orderOf z = 2) :
    z ∈ normalizer ((X D k ⊓ (X D k).map (MulAut.conj z).toMonoidHom : Subgroup G) : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_inf _ _ _ (MulAut.conj z).injective, map_map]
  have hf : (MulAut.conj z).toMonoidHom.comp (MulAut.conj z).toMonoidHom =
      MonoidHom.id G := by
    ext x
    change z * (z * x * z⁻¹) * z⁻¹ = x
    calc
      _ = z ^ 2 * x * (z ^ 2)⁻¹ := by simp only [pow_two]; group
      _ = x := by
        have hzsq : z ^ 2 = 1 := hz2 ▸ pow_orderOf_eq_one z
        rw [hzsq]; simp
  change (X D k).map (MulAut.conj z).toMonoidHom ⊓
    (X D k).map ((MulAut.conj z).toMonoidHom.comp (MulAut.conj z).toMonoidHom) = _
  rw [hf, map_id, inf_comm]

/-- A reflection outside N(F) cannot preserve the four-group E ∩ F. -/
public theorem reflection_not_normalizes_intersection (z : G)
    (hzE : z ∈ normalizer (CaseII.E D k : Set G))
    (hzF : z ∉ normalizer (CaseII.F D k : Set G)) :
    z ∉ normalizer ((CaseII.E D k ⊓ CaseII.F D k : Subgroup G) : Set G) :=
  fun hzV => hzF (CaseII.l27_normalizes_F_of_normalizes_intersection D k z hzE hzV)

omit [Finite G] in
/-- The actual generated subgroup Y preserves E. -/
public theorem Y_le_normalizer_E (z : G)
    (hzE : z ∈ normalizer (CaseII.E D k : Set G)) :
    Y D k w z ≤ normalizer (CaseII.E D k : Set G) :=
  sup_le (B_le_normalizer_E D k w) (zpowers_le.mpr hzE)

omit [Finite G] in
/-- B is normal relative to Y; no ambient normality is asserted. -/
public theorem B_normal_in_Y (z : G)
    (hzE : z ∈ normalizer (CaseII.E D k : Set G))
    (hzQ : z ∈ normalizer (zpowers w.actor : Set G)) :
    ((B D k w).subgroupOf (Y D k w z)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  exact sup_le le_normalizer (zpowers_le.mpr
    (normalizes_B_of_normalizes_E_and_actor D k w z hzE hzQ))

omit [Finite G] in
/-- The literal join consists precisely of B and its coset Bz. -/
public theorem mem_Y_iff (z : G) (hz2 : orderOf z = 2)
    (hzE : z ∈ normalizer (CaseII.E D k : Set G))
    (hzQ : z ∈ normalizer (zpowers w.actor : Set G)) (y : G) :
    y ∈ Y D k w z ↔ y ∈ B D k w ∨ ∃ b ∈ B D k w, b * z = y := by
  classical
  constructor
  · intro hy
    have hnorm : zpowers z ≤ normalizer (B D k w : Set G) :=
      zpowers_le.mpr (normalizes_B_of_normalizes_E_and_actor D k w z hzE hzQ)
    have hy' : y ∈ (B D k w : Set G) * (zpowers z : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ hnorm]
      exact hy
    obtain ⟨b, hb, t, ht, rfl⟩ := hy'
    have hzfin : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.mpr
      ⟨2, by decide, hz2 ▸ pow_orderOf_eq_one z⟩
    change t ∈ zpowers z at ht
    rw [hzfin.mem_zpowers_iff_mem_range_orderOf, hz2] at ht
    obtain ⟨i, hi, hit⟩ := Finset.mem_image.mp ht
    have hi2 := Finset.mem_range.mp hi
    have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl
    · have ht1 : t = 1 := by simpa using hit.symm
      exact Or.inl (by simpa [ht1] using hb)
    · have htz : t = z := by simpa using hit.symm
      exact Or.inr ⟨b, hb, by rw [htz]⟩
  · rintro (hy | ⟨b, hb, rfl⟩)
    · exact (show B D k w ≤ Y D k w z from le_sup_left) hy
    · exact mul_mem_sup hb (mem_zpowers z)

/-- The intersection Y ∩ X is B, independently of the harder intersection X ∩ Xᶻ. -/
public theorem Y_inf_X_of_reflection (L : LocalAnalysisData D k) (z : G)
    (hz2 : orderOf z = 2)
    (hzE : z ∈ normalizer (CaseII.E D k : Set G))
    (hzQ : z ∈ normalizer (zpowers w.actor : Set G))
    (hzF : z ∉ normalizer (CaseII.F D k : Set G)) :
    Y D k w z ⊓ X D k = B D k w := by
  apply le_antisymm
  · intro y hy
    rcases (mem_Y_iff D k w z hz2 hzE hzQ y).mp hy.1 with h | ⟨b, hb, he⟩
    · exact h
    · have hzX : z ∈ X D k := by
        have h := (X D k).mul_mem ((X D k).inv_mem (B_le_X D k L w hb)) hy.2
        simpa [← he] using h
      exact (hzF (X_le_normalizer_F D k hzX)).elim
  · exact le_inf le_sup_left (B_le_X D k L w)

/-- A reflection outside N(F) cannot preserve EF while preserving E. -/
public theorem reflection_not_normalizes_E_sup_F (z : G)
    (hzE : z ∈ normalizer (CaseII.E D k : Set G))
    (hzF : z ∉ normalizer (CaseII.F D k : Set G)) :
    z ∉ normalizer ((CaseII.E D k ⊔ CaseII.F D k : Subgroup G) : Set G) := by
  intro hzJ
  apply hzF
  let f := (MulAut.conj z).toMonoidHom
  have hE : (CaseII.E D k).map f = CaseII.E D k :=
    mem_normalizer_iff_map_conj_eq.mp hzE
  have hJ : (CaseII.E D k ⊔ CaseII.F D k).map f = CaseII.E D k ⊔ CaseII.F D k :=
    mem_normalizer_iff_map_conj_eq.mp hzJ
  have hFT : (CaseII.F D k).map f ≤ CaseII.caseIISylow D k :=
    ((map_mono (show CaseII.F D k ≤ CaseII.E D k ⊔ CaseII.F D k from
      le_sup_right)).trans_eq hJ).trans
      (sup_le (CaseII.E_le_caseIISylow D k) (CaseII.F_le_caseIISylow D k))
  let := CaseII.F_elementary D k
  have hc : Nat.card ((CaseII.F D k).map f) = 16 := by
    rw [card_map_of_injective (MulAut.conj z).injective, CaseII.F_card]
  rcases CaseII.elementary_sixteen_in_caseIISylow D k ((CaseII.F D k).map f) hFT
    (IsElementaryAbelian.map f) hc with he | hf
  · have hEF : CaseII.E D k = CaseII.F D k :=
      (map_injective (MulAut.conj z).injective) (hE.trans he.symm)
    have hcard := CaseII.l27_intersection_card D k
    rw [hEF, inf_idem, CaseII.F_card] at hcard
    contradiction
  · exact mem_normalizer_iff_map_conj_eq.mpr hf

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
