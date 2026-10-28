module
public import Theory.SpecificGroups.Rudvalis.Model.LowCentralizers.Maximality
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.SylowCenters
public import Theory.GroupTheory.DoubleCoverCentralizer.SylowCenterConjugacy

/-!
# Maximal two-central centralizers in Rudvalis

The marked max6 central involution is conjugate to b², which is central in
a certified Sylow subgroup. Centers of Sylow two-subgroups have order two,
so all two-central involution centralizers inherit max6's maximality.
Simplicity removes the ambient two-core; the odd-index maximal two-core
premise is discharged by the earlier source calculation in the ordinary
component adapter. The source component supplies simplicity there.

This is the intrinsic centralizer step for Aschbacher--Smith 15.1.20(3d),
printed pp.1096--1097. The original ATLAS degree-4060 carrier, word convention
and attribution are preserved in the imported certificate modules.
-/

public section
namespace Rudvalis.OrdinaryLocal
open Subgroup Theory.GroupTheory.DoubleCoverCentralizer
open SylowOvergroups
open SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate

private theorem twoCore_eq_bot [IsSimpleGroup Model] : pCore 2 Model = ⊥ := by
  rcases (inferInstance : (pCore 2 Model).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hp : IsPGroup 2 Model := by
      have hh := pCore_isPGroup (p := 2) (G := Model)
      rw [h] at hh
      exact hh.of_equiv (Subgroup.topEquiv)
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    have hd : 13 ∣ 2^n := by
      rw [← hn, ← orderOf_ab]
      exact orderOf_dvd_natCard _
    have hf : 13 ∣ 2 := (show Nat.Prime 13 by decide).dvd_of_dvd_pow hd
    norm_num at hf

/-- The actual two-central centralizer is maximal; only the independent
odd-index maximal two-core theorem is retained for the source adapter. -/
theorem twoCentral_centralizer_isCoatom [IsSimpleGroup Model]
    (hcore : OddIndexMaximalTwoCore) (t : Model) (ht : orderOf t = 2)
    (hc : TwoCentral t) : IsCoatom (centralizer ({t} : Set Model)) := by
  have hz : TwoCentral centralInvolution := by
    have hh := InvolutionCentralizers.square_twoCentral.map
      (MulAut.conj LowCentralizers.squareConjugator).symm
    rwa [← LowCentralizers.squareConjugator_alignment, MulEquiv.symm_apply_apply] at hh
  apply hc.centralizer_isCoatom_of_center_card_two hz
    (fun he => by rw [he,orderOf_one] at ht; omega)
    (fun he => by
      have ho := centralInvolution_order
      rw [he,orderOf_one] at ho
      omega)
    InvolutionCentralizers.sylow_center_card
  rw [← LowCentralizers.max6_eq_centralizer]
  exact LowCentralizers.max6_isCoatom_of_twoCore twoCore_eq_bot hcore
end Rudvalis.OrdinaryLocal
