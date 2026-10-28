module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Structure
public import Theory.GroupTheory.CComponent.FittingCentralizer
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Quasisimple components with three-group Fitting subgroup

In the nonquasisimple alternatives of A.3.6, the natural kernel has order
p² for p > 3, or every prime divisor of the nilpotent kernel is ±1 modulo
five or is five. Both kernels are three-free. If the actual Fitting
subgroup is a three-group, it is therefore trivial in either alternative;
the common quasisimple Fitting quotient is then the group itself.

The Chapter 14 local-component application uses subnormal monotonicity
of Fitting subgroups and source 14.7.6. No odd-core classification or
center–Frattini equality is required.

Source: Aschbacher–Smith A.3.6, printed pp.43–45; the quasisimplicity
clause of 14.7.30, printed p.1055, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem fitting_eq_bot_of_three_free {D : Type*} [Group D] [Finite D]
    (hp : IsPGroup 3 (fittingSubgroup D))
    (hf : ¬ 3 ∣ Nat.card (fittingSubgroup D)) : fittingSubgroup D = ⊥ := by
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  apply Subgroup.card_eq_one.mp
  rw [hn]
  have : n = 0 := by
    by_contra hne
    exact hf (hn ▸ dvd_pow_self 3 hne)
  rw [this,pow_zero]

/-- The nonquasisimple alternatives of A.3.6 have three-free Fitting
subgroup. A three-group Fitting subgroup therefore forces quasisimplicity. -/
theorem A36Conclusion.isQuasisimple_of_fitting_isThreeGroup
    {B : Subgroup G} (hB : B.IsCComponent) (h : A36Conclusion B)
    (hp : IsPGroup 3 (fittingSubgroup B)) : IsQuasisimple B := by
  have finish (hf : fittingSubgroup B = ⊥) : IsQuasisimple B := by
    let := hB.perfect
    let : IsQuasisimple (B ⧸ fittingSubgroup B) := h.2.2.1
    exact IsQuasisimple.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hf).trans QuotientGroup.quotientBot)
  cases h.1 with
  | simple hc hs hm => exact hc.2
  | cover hc hz hm => exact hc.2
  | natural hn =>
    apply finish
    apply fitting_eq_bot_of_three_free hp
    obtain ⟨he,p,hprime,hgt,F,_,_,hF,v,e,hv⟩ := hn
    have hc : Nat.card (generalizedFitting B) = p ^ 2 := by
      rw [Nat.card_congr v.toEquiv]
      change Nat.card (Fin 2 → F) = p ^ 2
      rw [Nat.card_fun,Nat.card_fin,hF]
    rw [←he,hc]
    intro hd
    rcases (Nat.dvd_prime hprime).mp (Nat.prime_three.dvd_of_dvd_pow hd) with heq | heq <;> omega
  | nilpotent hn =>
    apply finish
    apply fitting_eq_bot_of_three_free hp
    intro hd
    have hh := (hn.2.2.2 3 Nat.prime_three (hn.1.symm ▸ hd)).1
    norm_num at hh

end CFSG.Quasithin.Chapter1.Section02
