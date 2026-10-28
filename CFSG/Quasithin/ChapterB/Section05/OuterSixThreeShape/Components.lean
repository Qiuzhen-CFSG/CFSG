module

public import CFSG.Quasithin.ChapterB.Section05.OuterSixThreeShape
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.GroupTheory.QuasithinBasic
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Intrinsic factors in the outer A6–C3 source configuration

The specified multiplication isomorphism makes the two literal factors commute
and intersect trivially. Their conjugation witnesses and ambient generation
make both factors normal. The A6 factor is an ordinary component of three-rank
at least two, whereas the cubic factor lies in the Fitting subgroup. Consequently
the generalized Fitting subgroup cannot be quasisimple.

This is the group-only exclusion used in the rank-one case of G.6.4 after
B.5.7 forces quasisimple generalized Fitting. No fixed-space splitting or
extension-order assertion is inferred from the outer configuration.
Source: Aschbacher–Smith, B.5.6(4) and G.6.4, pp.105 and 345–346.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.OuterSixThreeShape
variable {D : Type*} [Group D] (c : OuterSixThreeShape D)

private theorem compatible_normalizer {A : Subgroup D} {t : D}
    (α : MulAut A) (ha : ∀ a : A, (α a : D) = t * a * t⁻¹) :
    t ∈ normalizer (A : Set D) := by
  rw [mem_normalizer_iff_map_conj_eq]
  apply le_antisymm
  · rintro _ ⟨a, haA, rfl⟩
    change t * a * t⁻¹ ∈ A
    simpa only [← ha ⟨a, haA⟩] using (α ⟨a, haA⟩).property
  · intro a haA
    refine ⟨(α.symm ⟨a, haA⟩ : A), (α.symm ⟨a, haA⟩).property, ?_⟩
    change t * _ * t⁻¹ = a
    rw [← ha]
    exact congrArg Subtype.val (α.apply_symm_apply ⟨a, haA⟩)

theorem first_second_commute (a : c.first) (b : c.second) :
    Commute (a : D) (b : D) := by
  have he : c.product ((a, 1) * (1, b)) = c.product ((1, b) * (a, 1)) := by simp
  rw [map_mul, map_mul] at he
  have hv := congrArg Subtype.val he
  change (a : D) * (b : D) = (b : D) * (a : D)
  simpa only [coe_mul, c.product_apply, coe_one, one_mul, mul_one] using hv

theorem first_normal : c.first.Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← c.generates]
  refine sup_le (sup_le c.first.le_normalizer ?_) (zpowers_le.mpr ?_)
  · apply le_trans (b := centralizer (c.first : Set D))
    · intro b hb
      exact mem_centralizer_iff.mpr fun a ha => c.first_second_commute ⟨a, ha⟩ ⟨b, hb⟩
    · exact centralizer_le_normalizer _
  · obtain ⟨α, ha, _⟩ := c.firstOuter
    exact compatible_normalizer α ha

theorem second_normal : c.second.Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← c.generates]
  refine sup_le (sup_le ?_ c.second.le_normalizer) (zpowers_le.mpr ?_)
  · apply le_trans (b := centralizer (c.second : Set D))
    · intro a ha
      exact mem_centralizer_iff.mpr fun b hb => (c.first_second_commute ⟨a, ha⟩ ⟨b, hb⟩).symm
    · exact centralizer_le_normalizer _
  · obtain ⟨α, ha, _⟩ := c.secondOuter
    exact compatible_normalizer α ha

theorem first_isComponent : IsComponent D c.first := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsQuasisimple (alternatingGroup (Fin 6)) := {
    toIsPerfect := inferInstance
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  exact ⟨c.first_normal.isSubnormal, IsQuasisimple.of_mulEquiv c.firstEquiv.symm⟩

theorem first_three_rank : 1 < primeRank 3 c.first := by
  let : Finite c.first := Finite.of_injective c.firstEquiv c.firstEquiv.injective
  rw [primeRank_equiv 3 c.firstEquiv]
  exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)

theorem factors_disjoint : Disjoint c.first c.second := by
  rw [disjoint_iff_inf_le]
  intro x hx
  have he : c.product (⟨x, hx.1⟩, 1) = c.product (1, ⟨x, hx.2⟩) := by
    apply Subtype.ext
    simp only [c.product_apply, coe_one, mul_one, one_mul]
  have hh := congrArg Prod.fst (c.product.injective he)
  exact congrArg Subtype.val hh

include c in
theorem not_quasisimple_fitting [Finite D]
    (hq : IsQuasisimple (generalizedFitting D)) : False := by
  let : c.second.Normal := c.second_normal
  have hp : IsPGroup 3 c.second := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_congr c.secondEquiv.toEquiv]
    simp)
  have hs : c.second ≤ pCore 3 D := le_sSup ⟨inferInstance, hp⟩
  have hf : IsComponent D (generalizedFitting D) := ⟨(inferInstance :
    (generalizedFitting D).Normal).isSubnormal, hq⟩
  have he : c.first = generalizedFitting D := c.first_isComponent.eq_of_le hf
    (component_le_generalizedFitting D _ c.first_isComponent)
  have hle : c.second ≤ c.first := he ▸
    hs.trans ((pCore_le_fitting D 3).trans (fitting_le_generalizedFitting D))
  have hb : c.second = ⊥ := bot_unique fun x hx => c.factors_disjoint.le_bot ⟨hle hx, hx⟩
  have hc : Nat.card c.second = 3 := by
    rw [Nat.card_congr c.secondEquiv.toEquiv]
    simp
  rw [hb, Nat.card_unique] at hc
  omega
end CFSG.Quasithin.ChapterB.OuterSixThreeShape
