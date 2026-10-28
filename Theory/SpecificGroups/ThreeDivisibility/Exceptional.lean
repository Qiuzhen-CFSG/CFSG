module

public import Theory.SpecificGroups.ProjectiveLinearThree
public import Theory.SpecificGroups.Triality.LeviIdentification
public import Theory.SpecificGroups.Triality.LeviRankOneMatrices
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.LinearCover.RankOne
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.Disjoint

public import Theory.SpecificGroups.Tits.Atlas1600Parrott

/-!
# Three-divisibility for triality, Ree and Tits carriers

The central root Levi in the genuine graph-field triality group is PSL₂(q),
so its order is divisible by three. In a supplied Ree fixed group, the
parameter-one elements in the two signed linear root blocks are distinct
involutions whose product has cube one. Their root formulas and the
opposition intersection prove this directly from `LocalBlockInput`.
For the Tits presentation, a concrete quotient contains an element of order
three; surjectivity then lifts divisibility to the presented carrier.

Only these small subgroups and quotient maps are needed. No construction of
the exceptional Ree endomorphism or order/simplicity certificate is assumed.

Sources: GLS3 §§2.4 and 2.6, `refs/KGroup/GLS3/chapter2.tex`;
Parrott (1972), p.683, as transcribed in the imported Tits modules.
Application: Aschbacher--Smith, 1.1.5(3) and 15.3.34, printed pp.501--503
and 1134 of `refs/quasithin.pdf`.
-/

public section
open Matrix Subgroup
open scoped MatrixGroups

namespace Triality.Standard
open Parabolics
theorem three_dvd_card (P : Parameters) (hp : P.prime = 2) : 3 ∣ Nat.card (Carrier P) := by
  have hd := ProjectiveSpecialLinearGroup.three_dvd_card
    (GaloisField P.prime P.exponent) 2 (by decide)
  rw [← Nat.card_congr
    (leviCentralEquivPSL2OfPinnedMaps P hp (pinnedRankOneMaps P hp)).toEquiv] at hd
  exact hd.trans (levi P .central).card_subgroup_dvd_card

theorem model_three_dvd_card {G : Type*} [Group G] {f : ℕ}
    (h : IsTrialityGroupAt (2 ^ f) G) : 3 ∣ Nat.card G := by
  obtain ⟨P, hq, ⟨e⟩⟩ := h
  have hd : P.prime ∣ P.q := dvd_pow_self P.prime (Nat.ne_of_gt P.exponent_pos)
  have hp : P.prime = 2 := Nat.prime_eq_prime_of_dvd_pow
    P.prime_prime Nat.prime_two (hq ▸ hd)
  rw [Nat.card_congr e.toEquiv]
  exact three_dvd_card P hp
end Triality.Standard

namespace ReeF4.LocalBlockInput
open PairRigidity PairRigidity.LocalIndices PairRigidity.BlockParameters.FieldRecovery LargeLocalSeeds
private theorem cube_of_involutions {G : Type*} [Group G] (a b : G)
    (ha : a * a = 1) (hb : b * b = 1)
    (hc : (a * b * a) * a * (a * b * a) = b) : (a * b) ^ 3 = 1 := by
  calc
    (a * b) ^ 3 = ((a * b * a) * a * (a * b * a)) * b := by
      simp only [pow_succ, pow_zero, mul_one, mul_assoc, ha, one_mul]
    _ = 1 := by rw [hc, hb]

theorem three_dvd_card {m : ℕ} (d : LocalBlockInput m) : 3 ∣ Nat.card d.fixedGroup := by
  let a := linearElement d true 1
  let b := linearElement d false 1
  have ha : a * a = 1 := linearElement_self_mul d true 1
  have hb : b * b = 1 := linearElement_self_mul d false 1
  have hc := linearPanelWeyl_conj_positive d (1 : CoefficientField m)
  have hw : linearPanelWeyl d 1 = a * b * a := by simp [linearPanelWeyl, a, b]
  have hconj : (a * b * a) * a * (a * b * a) = b := by
    rw [linearPanelWeyl_inv] at hc
    simpa only [hw] using hc
  have hcube : (a * b) ^ 3 = 1 := cube_of_involutions a b ha hb hconj
  have hab : a * b ≠ 1 := by
    intro h
    have he : a = b := (mul_eq_one_iff_eq_inv.mp h).trans (linearElement_inv d false 1)
    have haU : a ∈ standardUnipotent d :=
      simpleBlock_positive_le d .linear (linearElement_mem d true 1)
    have hbV : b ∈ oppositeUnipotent d :=
      simpleBlock_negative_le d .linear (linearElement_mem d false 1)
    have ha1 : a = 1 := Subgroup.disjoint_def.mp
      (PairNormalization.standardUnipotent_disjoint_opposite d) haU (he.symm ▸ hbV)
    have h10 : (1 : CoefficientField m) = 0 :=
      linearElement_injective d true (ha1.trans (linearElement_zero d true).symm)
    exact one_ne_zero h10
  have ho : orderOf (a * b) = 3 := orderOf_eq_prime hcube hab
  simpa only [ho] using _root_.orderOf_dvd_natCard (a * b)
end ReeF4.LocalBlockInput

namespace Theory.SpecificGroups.ThreeDivisibility

theorem tits : 3 ∣ Nat.card Tits.ParrottGroup := by
  let b : Tits.Atlas1600Group := ⟨Tits.atlas1600B, Tits.atlas1600B_mem⟩
  have hb : orderOf b = 3 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      apply Equiv.ext
      intro x
      exact Tits.atlas1600BMap_cube x
    · intro h
      have hh := congrArg (fun g : Tits.Atlas1600Group => g.val 0) h
      have hn : Tits.atlas1600B 0 ≠ (0 : Fin 1600) := by decide +kernel
      exact hn hh
  have hd : 3 ∣ Nat.card Tits.Atlas1600Group := by
    simpa only [hb] using orderOf_dvd_natCard b
  exact hd.trans (Subgroup.card_dvd_of_surjective _ Tits.atlas1600ParrottLift_surjective)

end Theory.SpecificGroups.ThreeDivisibility
