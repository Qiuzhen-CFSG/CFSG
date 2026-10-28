module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer
public import Theory.GroupTheory.PResidual.PCoreQuotient
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The intrinsic residual core quotient of the second Hall--Janko normalizer

The checked quotient by the order-64 radical is S₃ × C₃. Its two-residual is
A₃ × C₃, of order nine, and hence has trivial two-core. The actual quotient map
has two-group kernel, so the residual/core quotient transport theorem supplies
the same order nine for the literal full normalizer. This computes the
 two-residual, without identifying it with the derived subgroup.

Source application: Aschbacher--Smith 2.3.9(7), printed p.526; the local group
is GLS3 Table 5.3g. All quotients use intrinsic cores and the fixed ATLAS carrier.
-/

public section
open Subgroup
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.BlockSubnormalOrders
open Theory.GroupTheory Seed PairNormalizer

private theorem nine_card :
    Nat.card ((alternatingGroup (Fin 3)).prod (⊤ : Subgroup (Multiplicative (ZMod 3)))) = 9 := by
  rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    nat_card_alternatingGroup, Nat.card_fin, Nat.card_congr Subgroup.topEquiv.toEquiv]
  norm_num [Nat.card_eq_fintype_card, Nat.factorial]

private theorem model_residual_eq : pResidual 2 QuotientModel =
    (alternatingGroup (Fin 3)).prod (⊤ : Subgroup (Multiplicative (ZMod 3))) := by
  apply le_antisymm
  · apply sInf_le
    refine ⟨inferInstance, IsPGroup.of_card (n := 1) ?_⟩
    change ((alternatingGroup (Fin 3)).prod (⊤ : Subgroup (Multiplicative (ZMod 3)))).index = 2 ^ 1
    simp [Subgroup.index_prod]
  · intro x hx
    let y : (alternatingGroup (Fin 3)).prod (⊤ : Subgroup (Multiplicative (ZMod 3))) := ⟨x, hx⟩
    have hy : y ^ 9 = 1 := nine_card ▸ pow_card_eq_one' (x := y)
    have hx9 : x ^ 9 = 1 := congrArg Subtype.val hy
    exact mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 9).of_dvd_right (orderOf_dvd_of_pow_eq_one hx9))

private theorem model_residual_card : Nat.card (pResidual 2 QuotientModel) = 9 := by
  rw [model_residual_eq]
  exact nine_card

private theorem model_residual_core_eq_bot : pCore 2 (pResidual 2 QuotientModel) = ⊥ := by
  apply Subgroup.card_eq_one.mp
  rcases (pCore_isPGroup (p := 2) (G := pResidual 2 QuotientModel)).card_eq_or_dvd with h | h
  · exact h
  · have hd := h.trans (pCore 2 (pResidual 2 QuotientModel)).card_subgroup_dvd_card
    rw [model_residual_card] at hd
    norm_num at hd

/-- The intrinsic two-residual modulo its own two-core has order nine. -/
theorem residual_core_quotient_card :
    Nat.card (pResidual 2 p₂ ⧸ pCore 2 (pResidual 2 p₂)) = 9 := by
  obtain ⟨e⟩ := p₂_quotient_equiv
  let f : p₂ →* QuotientModel := e.toMonoidHom.comp (QuotientGroup.mk' _)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = q₂.subgroupOf p₂ := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hp : IsPGroup 2 f.ker := by
    rw [hk]
    exact q₂_isPGroup.comap_subtype
  rw [Nat.card_congr (f.pResidualCoreQuotientEquiv hf hp).toEquiv,
    model_residual_core_eq_bot, Nat.card_congr QuotientGroup.quotientBot.toEquiv]
  exact model_residual_card
end Sporadic.LeechRelated.J2.ExceptionalParabolics.BlockSubnormalOrders
