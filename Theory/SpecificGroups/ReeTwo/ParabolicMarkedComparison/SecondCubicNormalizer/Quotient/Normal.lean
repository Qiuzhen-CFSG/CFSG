module

public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.SecondCubicNormalizer.Quotient.Core

/-!
# Normality of the native cubic inner subgroup

A normalizer of the cubic subgroup preserves its fixed elements, hence their
inner automorphisms. Both defining factors of the order-24 subgroup are
therefore invariant under the actual order-96 normalizer. Its quotient has
order four. The maps and subgroups remain literal throughout.

Source: the binary Ree endpoint calculation in Aschbacher–Smith F.1.12/J.4.5.
-/

@[expose] public section
namespace ReeTwo.SylowModel.CubicAction
noncomputable section
open Subgroup

abbrev cubicNormalizer : Subgroup (MulAut A) := normalizer (zpowers cubic : Set (MulAut A))

theorem cubicInnerCore_le_normalizer : cubicInnerCore ≤ cubicNormalizer :=
  sup_le (fixedInner_le_centralizer.trans (centralizer_le_normalizer _)) (zpowers cubic).le_normalizer

theorem normalizer_preserves_fixedCore {α : MulAut A} (hα : α ∈ cubicNormalizer)
    {a : A} (ha : a ∈ fixedCore) : α a ∈ fixedCore := by
  have hγ : α⁻¹ * cubic * α ∈ zpowers cubic := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp (cubicNormalizer.inv_mem hα) cubic).mp (mem_zpowers cubic)
  have he : (α⁻¹ * cubic * α) a = a :=
    smul_eq_self_of_mem_zpowers hγ (show cubic • a = a from ha)
  have hh := congrArg α he
  change cubic (α a) = α a
  simpa only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.apply_symm_apply] using hh

theorem cubicNormalizer_le_fixedInner_normalizer :
    cubicNormalizer ≤ normalizer (fixedInner : Set (MulAut A)) := by
  apply le_normalizer_iff.mpr
  intro α hα β hβ
  obtain ⟨a,ha,rfl⟩ := hβ
  refine ⟨α a,normalizer_preserves_fixedCore hα ha,?_⟩
  apply MulEquiv.ext
  intro x
  simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem cubicNormalizer_le_core_normalizer :
    cubicNormalizer ≤ normalizer (cubicInnerCore : Set (MulAut A)) :=
  (le_inf cubicNormalizer_le_fixedInner_normalizer le_rfl).trans
    (normalizer_inf_normalizer_le_normalizer_sup fixedInner (zpowers cubic))

def innerCoreInNormalizer : Subgroup cubicNormalizer := cubicInnerCore.subgroupOf cubicNormalizer

instance innerCoreInNormalizer_normal : innerCoreInNormalizer.Normal :=
  normal_subgroupOf_of_le_normalizer cubicNormalizer_le_core_normalizer

abbrev CubicNormalizerQuotient := cubicNormalizer ⧸ innerCoreInNormalizer

theorem innerCoreInNormalizer_card : Nat.card innerCoreInNormalizer = 24 := by
  change Nat.card (cubicInnerCore.subgroupOf cubicNormalizer) = 24
  rw [Nat.card_congr (subgroupOfEquivOfLe cubicInnerCore_le_normalizer).toEquiv]
  exact cubicInnerCore_card

theorem cubicNormalizerQuotient_card : Nat.card CubicNormalizerQuotient = 4 := by
  have hc := innerCoreInNormalizer.card_mul_index
  rw [innerCoreInNormalizer_card,cubic_normalizer_card] at hc
  change Nat.card CubicNormalizerQuotient = _
  change 24 * Nat.card CubicNormalizerQuotient = 96 at hc
  omega
end
end ReeTwo.SylowModel.CubicAction
