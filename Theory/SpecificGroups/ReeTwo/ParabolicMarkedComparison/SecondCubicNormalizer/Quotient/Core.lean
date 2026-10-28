module

public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.SecondCubicNormalizer
public import Theory.GroupTheory.SubgroupProductCard
public import Theory.GroupTheory.PResidual.SubnormalSupplement
public import Mathlib.GroupTheory.PGroup

/-!
# The native cubic inner subgroup of order twenty-four

The eight cubic-fixed elements act faithfully by inner automorphisms: an
element in their kernel centralizes the cubic-orbit generator and is trivial
by the checked fixed-point census. Their two-group image commutes with the
order-three cubic subgroup, and the intersection is trivial.

Source: the actual binary Ree endpoint in Aschbacher–Smith F.1.12/J.4.5.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace ReeTwo.SylowModel.CubicAction
noncomputable section

def fixedCore : Subgroup A := cubic.toMonoidHom.eqLocus (MonoidHom.id A)
def fixedInner : Subgroup (MulAut A) := fixedCore.map MulAut.conj
def cubicInnerCore : Subgroup (MulAut A) := fixedInner ⊔ zpowers cubic

theorem fixedCore_card : Nat.card fixedCore = 8 := by
  change Nat.card {a : A // cubic a = a} = 8
  exact CollectedBitVectors.cubic_fixed_card

def fixedInnerHom : fixedCore →* MulAut A := MulAut.conj.comp fixedCore.subtype

theorem fixedInnerHom_injective : Function.Injective fixedInnerHom := by
  apply fixedInnerHom.ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro a ha
  apply Subtype.ext
  apply CollectedBitVectors.cubic_fixed_eq_one_of_commute (a : A) a.property
  have he := DFunLike.congr_fun ha (orbit 0)
  change (a : A) * orbit 0 * (a : A)⁻¹ = orbit 0 at he
  exact mul_inv_eq_iff_eq_mul.mp he

theorem fixedInnerHom_range : fixedInnerHom.range = fixedInner := by
  rw [fixedInnerHom, MonoidHom.range_comp, range_subtype]
  rfl

theorem fixedInner_card : Nat.card fixedInner = 8 := by
  rw [← fixedInnerHom_range, ← Nat.card_congr (MonoidHom.ofInjective fixedInnerHom_injective).toEquiv]
  exact fixedCore_card

theorem fixedInner_commutes_cubic (α : MulAut A) (hα : α ∈ fixedInner) : Commute α cubic := by
  obtain ⟨a,ha,rfl⟩ := hα
  apply MulEquiv.ext
  intro x
  change a * cubic x * a⁻¹ = cubic (a * x * a⁻¹)
  simp only [map_mul, map_inv]
  rw [show cubic a = a from ha]

theorem fixedInner_le_centralizer : fixedInner ≤ centralizer (zpowers cubic : Set (MulAut A)) := by
  rw [zpowers_eq_closure, centralizer_closure]
  intro α hα
  exact mem_centralizer_singleton_iff.mpr (fixedInner_commutes_cubic α hα).eq

theorem fixedInner_inf_zpowers_bot : fixedInner ⊓ zpowers cubic = ⊥ := by
  have htwo : IsPGroup 2 fixedInner := IsPGroup.of_card (n := 3) fixedInner_card
  have hthree : IsPGroup 3 (zpowers cubic) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,cubic_order]; rfl)
  exact (IsPGroup.disjoint_of_ne 2 3 (by decide) fixedInner (zpowers cubic) htwo hthree).eq_bot

theorem fixedInner_mul_comm : (fixedInner : Set (MulAut A)) * (zpowers cubic : Set (MulAut A)) =
    (zpowers cubic : Set (MulAut A)) * (fixedInner : Set (MulAut A)) := by
  ext α
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩
    exact ⟨b,hb,a,ha,fixedInner_le_centralizer ha b hb⟩
  · rintro ⟨b,hb,a,ha,rfl⟩
    exact ⟨a,ha,b,hb,(fixedInner_le_centralizer ha b hb).symm⟩

theorem cubicInnerCore_card : Nat.card cubicInnerCore = 24 := by
  have hc := card_set_mul_mul_card_inf fixedInner (zpowers cubic)
  rw [fixedInner_inf_zpowers_bot, card_bot, mul_one, fixedInner_card, Nat.card_zpowers,
    cubic_order, ← coe_sup_of_set_mul_comm fixedInner (zpowers cubic) fixedInner_mul_comm] at hc
  exact hc
end
end ReeTwo.SylowModel.CubicAction
