module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.ClassConstruction.FixedPoints
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.ClassConstruction.CentralizerReduction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ClassDistributions.Model
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ClassDistributions.NormalizerFusion.Actors

/-!
# The nine normalizer classes with fixed vectors

The seventeen conjugacy classes of the marked involution centralizer fuse into
exactly the nine representatives in `normalizerFixedRepresentative`. All fusion
here is internal to the actual normalizer of E. Transitivity on nonidentity
vectors lets us conjugate a nontrivial square or cube in E to the marked
involution. The resulting element is in its centralizer, where the seventeen
representatives leave just two square roots or one class of order-six cube
roots. The existing normalizer conjugator handles the two involutory actors.

For separation, element orders and the literal quotient by E leave only the
two special order-four representatives; the source nonfusion hypothesis
separates that pair. No ambient fusion assertion is used to produce an
internal normalizer conjugator. The two exports discharge exactly the fixed
branch inputs of `nonempty_normalizerClassData_of_class_branches`.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 5, printed pp.9–10.
-/

open Subgroup
noncomputable section
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy CaseII CaseII.Distribution

local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm

private theorem square_classes : ∀ i : Fin 17,
    localRepresentative i ^ 2 = z 0 → i = 10 ∨ i = 13 := by
  decide +kernel

private theorem cube_classes : ∀ i : Fin 17,
    localRepresentative i ^ 3 = z 0 → localRepresentative i ^ 2 ≠ 1 → i = 7 := by
  decide +kernel

private theorem localRepresentative_power (y : TwistedModel) (m : ℕ)
    (hy : y ^ m = z 0) : localRepresentative (localClass y) ^ m = z 0 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp ((localClass_conjugate y).pow m)
  rw [hy, (z_zero_mem_center.comm g).eq.symm, mul_inv_cancel_right] at hg
  exact hg.symm

private theorem fixed_conj_order {H : Type*} [Group H] {x y : H}
    (h : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq x).symm

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)

include L in
private theorem normalizer_power_conjugate (t : TwistedModel) (m : ℕ)
    (hm : (t ^ m).right = 1) (hne : t ^ m ≠ 1) :
    ∃ y : TwistedModel, IsConj (normalizerCentralizer D k t)
      (normalizerCentralizer D k y) ∧ y ^ m = z 0 := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := L.normalizer_E
  have hcard : Nat.card (eNormalizerQuotient D k) = 360 := by
    rw [Nat.card_congr (hK.symm.QuotientMulEquiv.trans eK).toEquiv,
      nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hmE : (normalizerCentralizer D k t) ^ m ∈
      (E D k).subgroupOf (normalizer (E D k : Set G)) := by
    rw [← map_pow, normalizerCentralizer_mem_E]
    exact hm
  let v : E D k := ⟨((normalizerCentralizer D k t) ^ m :
    normalizer (E D k : Set G)), hmE⟩
  have hv : v ≠ 1 := by
    intro h
    apply hne
    apply into_injective D k
    have he : (into D k t) ^ m = 1 := congrArg (fun w : E D k => (w : G)) h
    simpa only [map_pow, map_one] using he
  obtain ⟨g, hg⟩ := E_fusion_of_quotient_card D k hcard v
    (eNormalizerPoint D k) hv (eNormalizerPoint_ne_one D k)
  let x := g * normalizerCentralizer D k t * g⁻¹
  have hxpow : x ^ m = normalizerCentralizer D k (z 0) := by
    apply Subtype.ext
    change ((g : G) * into D k t * (g : G)⁻¹) ^ m = into D k (z 0)
    rw [conj_pow, into_z_zero D k]
    exact hg
  have hxC : (x : G) ∈ D.centralizer := by
    apply mem_centralizer_singleton_iff.mpr
    have he : (x : G) ^ m = D.z := by
      have he : (x : G) ^ m = into D k (z 0) :=
        congrArg (fun w : normalizer (E D k : Set G) => (w : G)) hxpow
      exact he.trans (into_z_zero D k)
    rw [← he]
    exact ((Commute.refl (x : G)).pow_right m).eq
  obtain ⟨y, hy⟩ := k.surjective ⟨x, hxC⟩
  have hyx : normalizerCentralizer D k y = x :=
    Subtype.ext (congrArg (fun w : D.centralizer => (w : G)) hy)
  refine ⟨y, isConj_iff.mpr ⟨g, hyx.symm⟩, ?_⟩
  apply normalizerCentralizer_injective D k
  rw [map_pow, hyx, hxpow]

include L in
private theorem normalizer_square_covered (t : TwistedModel)
    (hm : (t ^ 2).right = 1) (hne : t ^ 2 ≠ 1) :
    IsConj (normalizerCentralizer D k t) (normalizerFixedRepresentative D k 3) ∨
      IsConj (normalizerCentralizer D k t) (normalizerFixedRepresentative D k 4) := by
  obtain ⟨y, hty, hy⟩ := normalizer_power_conjugate D k L t 2 hm hne
  have hc := hty.trans ((normalizerCentralizer D k).map_isConj (localClass_conjugate y))
  rcases square_classes (localClass y) (localRepresentative_power y 2 hy) with h | h
  · apply Or.inl
    rw [h] at hc
    change IsConj (normalizerCentralizer D k t) (normalizerCentralizer D k (z 3 * a)) at hc
    exact hc
  · apply Or.inr
    rw [h] at hc
    change IsConj (normalizerCentralizer D k t) (normalizerCentralizer D k (z 1 * d)) at hc
    exact hc

include L in
private theorem normalizer_cube_covered (t : TwistedModel)
    (hm : (t ^ 3).right = 1) (hne : t ^ 3 ≠ 1) (h2 : t ^ 2 ≠ 1) :
    IsConj (normalizerCentralizer D k t) (normalizerFixedRepresentative D k 1) := by
  obtain ⟨y, hty, hy⟩ := normalizer_power_conjugate D k L t 3 hm hne
  have hc := hty.trans ((normalizerCentralizer D k).map_isConj (localClass_conjugate y))
  have hrep : localRepresentative (localClass y) ^ 2 ≠ 1 := by
    intro h
    have hc2 := hc.pow 2
    rw [← map_pow, ← map_pow, h, map_one, isConj_one_left] at hc2
    exact h2 (normalizerCentralizer_injective D k (hc2.trans (map_one _).symm))
  have h := cube_classes (localClass y) (localRepresentative_power y 3 hy) hrep
  rw [h] at hc
  change IsConj (normalizerCentralizer D k t) (normalizerCentralizer D k (c * z 0)) at hc
  exact hc

include L in
/-- Every element of the marked centralizer is conjugate, inside the actual
normalizer, to one of the nine fixed-vector representatives. -/
public theorem normalizerCentralizer_fixedRepresentative_covers (t : TwistedModel) :
    ∃ i : Fin 9, IsConj (normalizerCentralizer D k t)
      (normalizerFixedRepresentative D k i) := by
  suffices hs : ∀ j : Fin 17, ∃ i : Fin 9,
      IsConj (normalizerCentralizer D k (localRepresentative j))
        (normalizerFixedRepresentative D k i) by
    obtain ⟨i, hi⟩ := hs (localClass t)
    exact ⟨i, ((normalizerCentralizer D k).map_isConj (localClass_conjugate t)).trans hi⟩
  intro j
  fin_cases j
  · exact ⟨5, IsConj.refl _⟩
  · exact ⟨0, IsConj.refl _⟩
  · obtain ⟨y, hy, he⟩ := normalizer_power_conjugate D k L (z 1) 1
      (by decide +kernel) (by decide +kernel)
    rw [pow_one] at he
    rw [he] at hy
    exact ⟨0, hy⟩
  · obtain ⟨y, hy, he⟩ := normalizer_power_conjugate D k L (z 2) 1
      (by decide +kernel) (by decide +kernel)
    rw [pow_one] at he
    rw [he] at hy
    exact ⟨0, hy⟩
  · exact ⟨6, IsConj.refl _⟩
  · obtain ⟨n, hn, ha⟩ := normalizer_a_d_conjugate D k L.normalizer_E
    refine ⟨6, IsConj.symm (isConj_iff.mpr ⟨⟨n, hn⟩, ?_⟩)⟩
    apply Subtype.ext
    exact ha
  · exact ⟨7, IsConj.refl _⟩
  · exact ⟨1, IsConj.refl _⟩
  · exact ⟨1, normalizer_cube_covered D k L _
      (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩
  · exact ⟨1, normalizer_cube_covered D k L _
      (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩
  · exact ⟨3, IsConj.refl _⟩
  · rcases normalizer_square_covered D k L (z 1 * a)
      (by decide +kernel) (by decide +kernel) with h | h
    · exact ⟨3, h⟩
    · exact ⟨4, h⟩
  · exact ⟨8, IsConj.refl _⟩
  · exact ⟨4, IsConj.refl _⟩
  · rcases normalizer_square_covered D k L (z 3 * d)
      (by decide +kernel) (by decide +kernel) with h | h
    · exact ⟨3, h⟩
    · exact ⟨4, h⟩
  · rcases normalizer_square_covered D k L (z 1 * z 3 * d)
      (by decide +kernel) (by decide +kernel) with h | h
    · exact ⟨3, h⟩
    · exact ⟨4, h⟩
  · exact ⟨2, IsConj.refl _⟩

private def fixedModel (i : Fin 9) : TwistedModel :=
  localRepresentative (![1, 7, 16, 10, 13, 0, 4, 6, 12] i)

omit [Finite G] in
private theorem fixedModel_eq (i : Fin 9) :
    normalizerFixedRepresentative D k i = normalizerCentralizer D k (fixedModel i) := by
  fin_cases i <;> rfl

private theorem fixedModel_right : ∀ i : Fin 9,
    (fixedModel i).right = 1 ↔ i = 0 ∨ i = 5 := by
  decide +kernel

private theorem fixedModel_square_right : ∀ i : Fin 9,
    (fixedModel i ^ 2).right = 1 ↔ i = 0 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
  decide +kernel

omit [Finite G] in
private theorem fixed_order (i : Fin 9) :
    orderOf (normalizerFixedRepresentative D k i) = ![2, 6, 8, 4, 4, 1, 2, 3, 4] i := by
  rw [fixedModel_eq, orderOf_injective _ (normalizerCentralizer_injective D k)]
  unfold fixedModel
  rw [localRepresentative_order]
  fin_cases i <;> rfl

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
omit [Finite G] in
/-- The nine published fixed-vector representatives lie in distinct conjugacy
classes of the actual normalizer. -/
public theorem normalizerFixedRepresentative_distinct : Function.Injective
    (fun i : Fin 9 => ConjClasses.mk (normalizerFixedRepresentative D k i)) := by
  intro i j hij
  have hc := ConjClasses.mk_eq_mk_iff_isConj.mp hij
  have ho := fixed_conj_order hc
  rw [fixed_order, fixed_order] at ho
  have hmodel := hc
  rw [fixedModel_eq, fixedModel_eq] at hmodel
  have hz := right_power_invariant D k L hmodel 1
  simp only [pow_one, fixedModel_right] at hz
  have hs := right_power_invariant D k L hmodel 2
  simp only [fixedModel_square_right] at hs
  have hfour : ¬ IsConj (normalizerFixedRepresentative D k 3)
      (normalizerFixedRepresentative D k 4) := by
    intro h
    exact L.four_not_fused ((normalizer (E D k : Set G)).subtype.map_isConj h)
  have hcases : ∀ i j : Fin 9,
      (![2, 6, 8, 4, 4, 1, 2, 3, 4] i : ℕ) = ![2, 6, 8, 4, 4, 1, 2, 3, 4] j →
      (i = 0 ∨ i = 5 ↔ j = 0 ∨ j = 5) →
      (i = 0 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ↔
        j = 0 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6) →
      i = j ∨ (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) := by decide
  rcases hcases i j ho hz hs with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h
  · exact (hfour hc).elim
  · exact (hfour hc.symm).elim

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
