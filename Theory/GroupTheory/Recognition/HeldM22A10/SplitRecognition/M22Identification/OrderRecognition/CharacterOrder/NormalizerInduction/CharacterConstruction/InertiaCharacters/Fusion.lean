module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.InertiaCharacters.ClassSums
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ClassDistributions.NormalizerFusion
/-!
# Internal fusion of the seventeen marked centralizer classes

The nine-class coverage theorem, element orders and the actual quotient by E
identify every local class except the last order-four pair. The existing actor
conjugator fixes the class of z₂a and proves that the last pair belongs to
opposite classes. Both possible assignments are retained for the character
norm calculation to distinguish. All positive conjugacy witnesses lie inside
N(E); ambient nonfusion is used only to rule out an internal identification.

Source: Janko, *A characterization of the Mathieu simple groups, I* (1968),
Section 5, pp.9–10.
-/

open Subgroup
noncomputable section
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy CaseII CaseII.Distribution
local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
private def fixedModel (i : Fin 9) : TwistedModel :=
  localRepresentative (![1, 7, 16, 10, 13, 0, 4, 6, 12] i)
private theorem fixed_order_model (i : Fin 9) :
    orderOf (fixedModel i) = ![2, 6, 8, 4, 4, 1, 2, 3, 4] i := by
  unfold fixedModel
  rw [localRepresentative_order]
  fin_cases i <;> rfl
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
omit [Finite G] in
private theorem fixed_model (i : Fin 9) :
    normalizerFixedRepresentative D k i = normalizerCentralizer D k (fixedModel i) := by
  fin_cases i <;> rfl
omit [Finite G] in
private theorem order_eq {x y : normalizer (E D k : Set G)} (h : IsConj x y) :
    orderOf x = orderOf y := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq x).symm
include L in
private theorem three_six (t : TwistedModel) (n : Fin 2)
    (ho : orderOf t = (![3, 6] n : ℕ)) :
    IsConj (normalizerCentralizer D k t)
      (normalizerFixedRepresentative D k (![7, 1] n)) := by
  obtain ⟨i, hi⟩ := normalizerCentralizer_fixedRepresentative_covers D k L t
  have he := order_eq D k hi
  rw [fixed_model, orderOf_injective _ (normalizerCentralizer_injective D k),
    orderOf_injective _ (normalizerCentralizer_injective D k), ho, fixed_order_model] at he
  have hh : ∀ (n : Fin 2) (i : Fin 9),
      (![3, 6] n : ℕ) = ![2, 6, 8, 4, 4, 1, 2, 3, 4] i → i = (![7, 1] n : Fin 9) := by decide
  rwa [hh n i he] at hi
include L in
omit [Finite G] in
private theorem right_power_invariant {t s : TwistedModel}
    (h : IsConj (normalizerCentralizer D k t) (normalizerCentralizer D k s)) (m : ℕ) :
    (t ^ m).right = 1 ↔ (s ^ m).right = 1 := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := L.normalizer_E
  have hc := (normalizerQuotient D k K hK eK).map_isConj (h.pow m)
  rw [← map_pow, ← map_pow] at hc
  rw [← normalizerQuotient_centralizer_eq_one_iff D k K hK eK,
    ← normalizerQuotient_centralizer_eq_one_iff D k K hK eK]
  constructor
  · intro he
    simpa only [he, isConj_one_right] using hc
  · intro he
    simpa only [he, isConj_one_left] using hc
include L in
private theorem square_four (t : TwistedModel) (ho : orderOf t = 4)
    (hs : (t ^ 2).right = 1) :
    IsConj (normalizerCentralizer D k t) (normalizerFixedRepresentative D k 3) ∨
      IsConj (normalizerCentralizer D k t) (normalizerFixedRepresentative D k 4) := by
  obtain ⟨i, hi⟩ := normalizerCentralizer_fixedRepresentative_covers D k L t
  have he := order_eq D k hi
  rw [fixed_model, orderOf_injective _ (normalizerCentralizer_injective D k),
    orderOf_injective _ (normalizerCentralizer_injective D k), ho, fixed_order_model] at he
  have hh : ∀ i : Fin 9, (4 : ℕ) = ![2, 6, 8, 4, 4, 1, 2, 3, 4] i →
      i = 3 ∨ i = 4 ∨ i = 8 := by decide
  rcases hh i he with rfl | rfl | rfl
  · exact Or.inl hi
  · exact Or.inr hi
  · have hx := (right_power_invariant D k L hi 2).mp hs
    exact False.elim (by
      change ((b * d) ^ 2).right = 1 at hx
      exact (by decide +kernel : ((b * d) ^ 2).right ≠ 1) hx)
include L in
private theorem vector_conj (t : TwistedModel) (hr : t.right = 1) (hne : t ≠ 1) :
    IsConj (normalizerCentralizer D k t) (normalizerFixedRepresentative D k 0) := by
  obtain ⟨i, hi⟩ := normalizerCentralizer_fixedRepresentative_covers D k L t
  have hz : (fixedModel i).right = 1 := by
    have h := right_power_invariant D k L (by simpa only [fixed_model] using hi) 1
    simpa only [pow_one] using h.mp (by simpa using hr)
  have hh : ∀ i : Fin 9, (fixedModel i).right = 1 → i = 0 ∨ i = 5 := by decide +kernel
  rcases hh i hz with rfl | rfl
  · exact hi
  · change IsConj (normalizerCentralizer D k t) (normalizerCentralizer D k 1) at hi
    rw [map_one, isConj_one_left] at hi
    exact (hne (normalizerCentralizer_injective D k (hi.trans (map_one _).symm))).elim

include L in
/-- The complete internal class fusion, retaining the two possible assignments of the last pair. -/
public theorem exists_normalizerInertiaFusion : ∃ swap : Bool, ∀ i : Fin 17,
    IsConj (normalizerCentralizer D k (localRepresentative i))
      (normalizerFixedRepresentative D k (normalizerInertiaFusionIndex swap i)) := by
  obtain ⟨n, hn, ha⟩ := normalizer_a_d_conjugate D k L.normalizer_E
  obtain ⟨hf11, hne⟩ := remaining_four_fusion_of_actor_conjugator D k n hn ha
  have h11 : IsConj (normalizerCentralizer D k (z 1 * a))
      (normalizerFixedRepresentative D k 4) := by
    rcases square_four D k L (z 1 * a) (localRepresentative_order 11)
      (by decide +kernel) with h | h
    · exact (L.four_not_fused
        (((normalizer (E D k : Set G)).subtype.map_isConj h).symm.trans hf11)).elim
    · exact h
  have h14 := square_four D k L (z 3 * d) (localRepresentative_order 14) (by decide +kernel)
  have h15 := square_four D k L (z 1 * z 3 * d) (localRepresentative_order 15) (by decide +kernel)
  have hpair : ∃ swap : Bool,
      IsConj (normalizerCentralizer D k (z 3 * d))
        (normalizerFixedRepresentative D k (if swap then 4 else 3)) ∧
      IsConj (normalizerCentralizer D k (z 1 * z 3 * d))
        (normalizerFixedRepresentative D k (if swap then 3 else 4)) := by
    rcases h14 with h14 | h14 <;> rcases h15 with h15 | h15
    · exact (hne ((normalizer (E D k : Set G)).subtype.map_isConj (h14.trans h15.symm))).elim
    · exact ⟨false, h14, h15⟩
    · exact ⟨true, h14, h15⟩
    · exact (hne ((normalizer (E D k : Set G)).subtype.map_isConj (h14.trans h15.symm))).elim
  obtain ⟨swap, h14, h15⟩ := hpair
  refine ⟨swap, ?_⟩
  intro i
  fin_cases i
  · exact IsConj.refl _
  · exact IsConj.refl _
  · exact vector_conj D k L _ (by decide +kernel) (by decide +kernel)
  · exact vector_conj D k L _ (by decide +kernel) (by decide +kernel)
  · exact IsConj.refl _
  · apply IsConj.symm
    apply isConj_iff.mpr
    refine ⟨⟨n, hn⟩, ?_⟩
    apply Subtype.ext
    exact ha
  · exact IsConj.refl _
  · exact IsConj.refl _
  · exact three_six D k L _ 1 (localRepresentative_order 8)
  · exact three_six D k L _ 1 (localRepresentative_order 9)
  · exact IsConj.refl _
  · exact h11
  · exact IsConj.refl _
  · exact IsConj.refl _
  · exact h14
  · exact h15
  · exact IsConj.refl _
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
