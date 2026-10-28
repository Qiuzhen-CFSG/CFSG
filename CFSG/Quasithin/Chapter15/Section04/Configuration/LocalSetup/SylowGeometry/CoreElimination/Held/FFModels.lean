module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.Held.Models
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.QuasisimpleModels
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Coordinates
public import Theory.SpecificGroups.SymplecticFour.Sylow
public import Theory.AtlasPort.LinearGroups.G2.LieSylowCenter
public import Theory.GroupTheory.CentralizerResidualProducts

/-!
# Held does not occur in the complete B.5.1 model list

The actual Held Sylow center has order two. Symplectic four-space Sylow
centers have order q²; the G₂ Sylow center has order q, forcing its binary
endpoint, whose order is prime to seventeen. The remaining alternatives are
excluded by the already proved rank-one, linear-three, bounded alternating,
central-cover and binary-linear comparisons on the same concrete carrier.

This rules out all ten models without a Held order or module-dimension input.
Source: Aschbacher--Smith B.5.1 and the retained Held branch of 15.4.20.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.HeldModels
open TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

private theorem model_sylow_center_card {A : Type*} [Group A] [Finite A]
    (e : Held.He ≃* A) (P : Sylow 2 A) : Nat.card (center P) = 2 := by
  let Q := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact (Nat.card_congr (centerCongr (e.symm.subgroupMap (P : Subgroup A))).toEquiv).trans
    (Held.LocalPairs.SylowGeometry.inner_center_card Q)

private theorem model_center_bot {A : Type*} [Group A] (e : Held.He ≃* A) : center A = ⊥ := by
  have he := congrArg (Subgroup.map e.toMonoidHom) Held.LocalPairs.center_eq_bot
  simpa only [map_center_equiv, Subgroup.map_bot] using he

theorem not_ff_model : ¬ QuasisimpleModel Held.He := by
  intro h
  cases h with
  | linearTwo F e =>
    by_cases hn : 1 < F.degree
    · let f := e.trans (QuotientGroup.quotientBot.symm.trans
        (QuotientGroup.quotientMulEquivOfEq (model_center_bot e).symm))
      exact not_even_rankOne hn ⟨F.Carrier,inferInstance,inferInstance,F.card_eq,⟨f⟩⟩
    · have hdeg : F.degree = 1 := by have := F.degree_pos; omega
      have hd := seventeen_dvd_card
      rw [Nat.card_congr e.toEquiv, Atlas.card_sl_two, F.card_eq, hdeg] at hd
      norm_num at hd
  | linearThree F e => exact not_full_linearThree F.degree_pos F.card_eq ⟨e⟩
  | symplecticFour F e =>
    let P := Theory.SpecificGroups.SymplecticFour.unipotentSylow F.card_eq F.degree_pos
    have hc := model_sylow_center_card e P
    change Nat.card (center (Theory.SpecificGroups.SymplecticFour.unipotent (F := F.Carrier))) = 2 at hc
    have he := Nat.card_congr (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.centerEquiv (F := F.Carrier)).toEquiv
    rw [Nat.card_prod, hc] at he
    change Nat.card F.Carrier * Nat.card F.Carrier = 2 at he
    have htwo : 2 ≤ Nat.card F.Carrier := by
      rw [F.card_eq]
      simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2)
        (show 1 ≤ F.degree from F.degree_pos)
    nlinarith
  | g2 F e =>
    let P := Atlas.G2.LieParabolicSetup.sylow (F := F.Carrier)
    have hc := model_sylow_center_card e P
    have he := Nat.card_congr (Atlas.G2.LieParabolicSetup.centerEquivHighestRoot
      (Atlas.G2.unipotent (K := F.Carrier))
      (Atlas.G2.LieParabolicSetup.fiveRootSubgroup_le_unipotent _ _) le_rfl).toEquiv
    have hcard : Nat.card F.Carrier = 2 := he.symm.trans hc
    have hd := seventeen_dvd_card
    rw [Nat.card_congr e.toEquiv, Atlas.G2.card_Model, hcard] at hd
    norm_num at hd
  | alternatingSix e => exact not_alternating (by decide) ⟨e⟩
  | alternatingSeven e => exact not_alternating (by decide) ⟨e⟩
  | tripleSix c _ =>
    have hc := Nat.card_congr c.toEquiv
    rw [Held.LocalPairs.center_eq_bot, card_bot] at hc
    norm_num at hc
  | g2DerivedTwo e =>
    have hc : Nat.card Held.He = 6048 := by
      rw [Nat.card_congr e.toEquiv, Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
      exact Atlas.G2.BinaryException.card_H
    have hd := seventeen_dvd_card
    rw [hc] at hd
    norm_num at hd
  | linearFourTwo e =>
    let f := e.trans (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq (model_center_bot e).symm))
    exact ComponentElimination.BinaryModels.sporadic_separation .he (Or.inl rfl)
      (by intro h; cases h) ⟨ZMod 2,inferInstance,inferInstance,by simp,⟨f⟩⟩
  | linearFiveTwo e =>
    let f := e.trans (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq (model_center_bot e).symm))
    exact ComponentElimination.BinaryModels.sporadic_separation .he (Or.inr rfl)
      (by intro h; cases h) ⟨ZMod 2,inferInstance,inferInstance,by simp,⟨f⟩⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.HeldModels

