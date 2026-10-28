module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.ModelComparison.Inputs
public import Theory.SpecificGroups.Triality.ModelSeparation.TwoSubgroup
public import Theory.SpecificGroups.Triality.ModelSeparation.LeviObstructions
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Triality cannot be a nonnormal component model

The positive fixed-root group is a nonabelian two-group, whereas binary
PSL₂ has elementary abelian Sylow two-subgroups. The cubic arm root group
excludes odd PSL₂, whose Sylow two-subgroups are dihedral. The arm Levi
also forces nine to divide the order, excluding both Suzuki and J₁.

This applies the intrinsic Theory model comparisons directly to the actual
group, without passing through a later chapter theorem. The resulting
exclusion is consumed by the complete field-indexed case split in
`ModelComparison`. Its argument works even at field exponent one.

Source: Aschbacher–Smith, comparison of 1.1.5(3a) and 1.2.1(3) in the
proof of 13.6.6, printed p.927. Root-model facts: GLS3 §§2.4–2.6.
-/

public section
open Subgroup Theory.GroupTheory Triality.Standard
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent.ModelComparison
open Chapter1.Section02

/-- Exclude all four actual nonnormal models using the genuine triality carrier. -/
theorem triality_not_nonnormal {Q : Type*} [Group Q] {f : ℕ}
    (hf : 1 ≤ f) (htriality : IsTrialityGroupAt (2 ^ f) Q) :
    ¬ NonnormalCComponentModel Q := by
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff Q f hf).mp htriality
  intro hm
  cases hm with
  | linear_even n hn iso =>
    obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := iso
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact ModelSeparation.not_equiv_binary_psl2 f hf F (e.symm.trans eF)
  | suzuki n hn iso =>
    obtain ⟨eS⟩ := iso
    have hd := ModelSeparation.nine_dvd_card f hf
    rw [Nat.card_congr (e.symm.trans eS).toEquiv] at hd
    exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free n hn
      ((by decide : 3 ∣ 9).trans hd)
  | linear_prime p hp ho iso =>
    obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := iso
    exact ModelSeparation.not_equiv_odd_psl2 f hf F
      ⟨p, 1, hp, ho, by decide, by simpa only [pow_one] using hF⟩ (e.symm.trans eF)
  | janko iso =>
    obtain ⟨eJ⟩ := iso
    have hd := ModelSeparation.nine_dvd_card f hf
    rw [Nat.card_congr (e.symm.trans eJ).toEquiv, Janko1.card_model] at hd
    norm_num at hd

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent.ModelComparison
