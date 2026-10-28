module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.ClassConstruction.FixedPoints
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.FusionSylow.FusedNine.IntersectionExistence
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.FusionSylow.FusedNine.IntersectionFixedPoints
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.FusionSylow.FusedNine.ComplementFusion
public import Theory.GroupAction.FiveActionMinimalOrder
public import Theory.GroupAction.FourthPowerFixed

/-!
# Actual odd-order witnesses for the normalizer class table

The source intersection of the E and F normalizers provides an element of
order three acting without nonidentity fixed vectors on E. The existing
two-class theorem then gives coverage of every fixed-point-free element of
order three by this witness. Cauchy's theorem gives an element of order five;
faithfulness of the action modulo E and the order-sixteen orbit calculation
show that every element of order five, including its square, is fixed-point-free.

These constructions supply actual elements, without assuming the remaining
conjugacy-class coverage or the character table.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Sections 3 and 5, pp.7–10.
-/

open Subgroup
noncomputable section
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)

include L
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

public theorem exists_normalizer_fixedPointFree_three :
    ∃ c₁ : normalizer (CaseII.E D k : Set G),
      orderOf c₁ = 3 ∧ ¬ normalizerHasFixedVector D k c₁ := by
  let h2 : InvolutionNormalizerData D k :=
    ⟨L.normalizer_E, L.normalizer_F, L.involution_fusion⟩
  obtain ⟨c, hcE, hcF, hc⟩ := exists_three_in_normalizer_intersection D k h2
  refine ⟨⟨c, hcE⟩, (orderOf_coe _).symm.trans hc, ?_⟩
  rintro ⟨v, hv, hf⟩
  apply hv
  apply Subtype.ext
  exact intersection_three_fixed_point_free D k h2 c hcE hcF hc v v.property
    (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hf))

public theorem normalizer_fixedPointFree_three_conjugate
    (c₁ : normalizer (CaseII.E D k : Set G))
    (hc₁ : orderOf c₁ = 3) (hfree : ¬ normalizerHasFixedVector D k c₁)
    (x : normalizer (CaseII.E D k : Set G)) (hx : orderOf x = 3)
    (hxfree : ¬ normalizerHasFixedVector D k x) : IsConj x c₁ := by
  have hc : orderOf (normalizerCentralizer D k CaseII.c) = 3 := by
    rw [orderOf_injective _ (normalizerCentralizer_injective D k)]
    exact CaseII.actor_orders.2.2.1
  have hfixed := normalizerCentralizer_hasFixedVector D k CaseII.c
  rcases normalizer_E_three_trichotomy D k L.normalizer_E x
    (normalizerCentralizer D k CaseII.c) c₁ hx hc hc₁ with h | h | h
  · exact (hxfree ((normalizerHasFixedVector_isConj D k h).mpr hfixed)).elim
  · exact h
  · exact (hfree ((normalizerHasFixedVector_isConj D k h).mp hfixed)).elim

public theorem normalizer_five_has_noFixedVector
    (x : normalizer (CaseII.E D k : Set G)) (hx : orderOf x = 5) :
    ¬ normalizerHasFixedVector D k x := by
  let a := normalizerConjugation D k x
  have ha : orderOf a = 5 := by
    apply orderOf_eq_prime
    · rw [show a ^ 5 = normalizerConjugation D k (x ^ 5) from (map_pow _ _ _).symm,
        ← hx, pow_orderOf_eq_one, map_one]
    · intro h
      have hm : x ∈ (CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G)) := by
        rw [← normalizerConjugation_ker D k L]
        exact h
      have hd := ((CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G))).orderOf_dvd_natCard hm
      rw [hx, Nat.card_congr (subgroupOfEquivOfLe (CaseII.E D k).le_normalizer).toEquiv,
        L.E_card] at hd
      norm_num at hd
  have hne : a ≠ 1 := by intro h; simp [h] at ha
  have hproper : FixedPoints.subgroup (zpowers a) (CaseII.E D k) ≠ ⊤ := by
    intro h
    apply hne
    apply DFunLike.ext
    intro v
    exact (MulAut.mem_fixed_zpowers_iff a v).mp (h ▸ mem_top v)
  have hbot := Theory.GroupAction.fixed_eq_bot_of_five_action_card_sixteen
    (by rw [Nat.card_zpowers, ha]) L.E_card hproper
  apply (normalizer_fixedPointFree_iff D k x).mp
  intro v hv
  have hm := (MulAut.mem_fixed_zpowers_iff a v).mpr hv
  rwa [hbot, mem_bot] at hm

public theorem exists_normalizer_fixedPointFree_five :
    ∃ μ : normalizer (CaseII.E D k : Set G),
      orderOf μ = 5 ∧ ¬ normalizerHasFixedVector D k μ ∧
        ¬ normalizerHasFixedVector D k (μ ^ 2) := by
  obtain ⟨μ, hμ⟩ := exists_prime_orderOf_dvd_card'
    (G := normalizer (CaseII.E D k : Set G)) 5 (by rw [normalizer_E_card D k L]; decide)
  refine ⟨μ, hμ, normalizer_five_has_noFixedVector D k L μ hμ,
    normalizer_five_has_noFixedVector D k L (μ ^ 2) ?_⟩
  rw [orderOf_pow' _ (by decide), hμ]
  decide

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
