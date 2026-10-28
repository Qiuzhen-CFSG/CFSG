module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.ModelComparison.Inputs
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.LieParameter.SplitModels
public import Theory.SpecificGroups.ThreeDivisibility.Classical
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.SpecificGroups.Janko1.Model.Certification.Order

/-!
# Excluding G₂ from the nonnormal component list

The split-octonion order has a two-part of at least q⁶. A binary PSL₂
with this two-part has larger total order; the existing intrinsic order
comparison excludes odd-prime PSL₂ as well. Three-divisibility excludes
Suzuki, and divisibility by sixteen excludes the certified J₁ carrier.
All comparisons retain the supplied group isomorphisms.

The imported Chapter 15 comparison is an intrinsic order lemma, independent
of that chapter's source theorem. Its octonion and matrix counts are from
the licensed ATLAS port, whose attribution is retained in the imports.
This supplies the G₂ field of `ExceptionalExclusions`.

Source: Aschbacher–Smith, 1.1.5(3a,b), pp.501–503, and 1.2.1(3), p.504,
compared in the moving-component paragraph of 13.6.6, p.927.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent.ModelComparison
open Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels

private theorem g2_not_binary {Q : Type*} [Group Q] {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hpsl : ClassicalGroup.IsPSL Q 2 (2^n))
    (hg2 : ClassificationModels.IsG2At Q (2^m)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hg2
  have hc := Nat.card_congr e.toEquiv
  rw [Atlas.G2.card_Model, hF] at hc
  have hp := psl_two_card_mul hpsl
  have hnpos : 0 < 2^n := by positivity
  have he : Even (2^n) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
  have ho : Odd (2^n-1) := Nat.Even.sub_odd hnpos he odd_one
  rw [Nat.coprime_two_left.mpr ho, mul_one] at hp
  have hd : 2^(m*6) ∣ Nat.card Q := by
    rw [hc, pow_mul]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hodd : Odd ((2^n)^2-1) :=
    Nat.Even.sub_odd (by have := pow_pos hnpos 2; omega)
      (he.pow_of_ne_zero (by decide)) odd_one
  have hd' : 2^(m*6) ∣ 2^n := by
    rw [hp] at hd
    exact ((Nat.coprime_two_left.mpr hodd).pow_left _).dvd_mul_right.mp hd
  have hl : (2^m)^6 ≤ 2^n := by
    simpa only [pow_mul] using Nat.le_of_dvd hnpos hd'
  let q := 2^m
  have hq : 4 ≤ q := by
    simpa only [q] using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hm
  have hq6 : q^2 < q^6 := pow_lt_pow_right₀ (by omega) (by decide)
  have hlt : (q^6-1)*(q^2-1) < (q^6)^2-1 := by
    have h1 : q^6-1+1=q^6 := Nat.sub_add_cancel (by have := pow_pos (by omega : 0 < q) 6; omega)
    have h2 : q^2-1+1=q^2 := Nat.sub_add_cancel (by have := pow_pos (by omega : 0 < q) 2; omega)
    have h3 : (q^6)^2-1+1=(q^6)^2 := Nat.sub_add_cancel (by have := pow_pos (pow_pos (by omega : 0 < q) 6) 2; omega)
    nlinarith
  have hmultiply := Nat.mul_lt_mul_of_pos_left hlt (show 0 < q^6 by positivity)
  have hmono := Nat.mul_le_mul hl
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left hl 2) 1)
  have hc' : Nat.card Q = q^6*((q^6-1)*(q^2-1)) := by rw [hc]; ring
  have hbad : Nat.card Q < Nat.card Q := calc
    Nat.card Q = q^6*((q^6-1)*(q^2-1)) := hc'
    _ < q^6*((q^6)^2-1) := hmultiply
    _ ≤ 2^n*((2^n)^2-1) := hmono
    _ = Nat.card Q := hp.symm
  exact (lt_irrefl _) hbad

open Chapter1.Section02
/-- The genuine octonion group is absent from all four nonnormal alternatives. -/
theorem g2_not_nonnormal {Q : Type*} [Group Q] {m : ℕ} (hm : 2 ≤ m)
    (hg2 : ClassificationModels.IsG2At Q (2^m)) : ¬ NonnormalCComponentModel Q := by
  intro h
  cases h with
  | linear_even n hn iso => exact g2_not_binary hn hm iso hg2
  | suzuki n hn iso =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hg2
    obtain ⟨eS⟩ := iso
    have hd := Theory.SpecificGroups.ThreeDivisibility.g2 F
    rw [Nat.card_congr (e.symm.trans eS).toEquiv] at hd
    exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free n hn hd
  | linear_prime p hp ho iso =>
    exact LieParameter.not_g2 ho hp.two_le hm iso hg2
  | janko iso =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hg2
    obtain ⟨eJ⟩ := iso
    have hc := Nat.card_congr (e.symm.trans eJ).toEquiv
    rw [Atlas.G2.card_Model, hF, Janko1.card_model] at hc
    have hd : 2^(m*6) ∣ 175560 := by
      rw [← hc, pow_mul]
      exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    have h16 : 2^4 ∣ 2^(m*6) := Nat.pow_dvd_pow 2 (by omega)
    have hh := h16.trans hd
    norm_num at hh

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent.ModelComparison
