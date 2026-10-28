module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# Rank-one order exclusions in the A.3.12 specialization

A cover of PSL₃(4) with center of order at most four has order divisible by
20160 and at most 80640. The order formulas for SL₂(q) and PSL₂(q) reduce
compatibility to a multiple of 20160 of the form q(q²−1), at most 161280.
Monotonicity bounds q by 54, and the finite arithmetic check excludes all
these values. No field or simple-group recognition by order is used.

Source: Aschbacher--Smith, A.3.12(2),(8),(9), printed pp.47--48, as used
on p.1136. The matrix order formula is the checked standalone SL₂ order API,
adapted there from Huppert II.6.14.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry.A312Specialization
open Chapter1.Section02.LocalModels

private theorem no_rankOne_order (q : ℕ) (hq : 2 ≤ q)
    (hd : 20160 ∣ q * (q ^ 2 - 1)) (hu : q * (q ^ 2 - 1) ≤ 161280) : False := by
  have hlt : q < 55 := by
    by_contra hn
    have hq55 : 55 ≤ q := by omega
    have hsq : 3025 ≤ q ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul hq55 hq55
    have hs : 3024 ≤ q ^ 2 - 1 := by omega
    have hprod := Nat.mul_le_mul hq55 hs
    omega
  interval_cases q <;> norm_num at hd

/-- The size interval of the actual cover excludes every PSL₂ model. -/
theorem no_psl_two_of_card {X : Type*} [Group X]
    (hd : 20160 ∣ Nat.card X) (hu : Nat.card X ≤ 80640) (q : ℕ) :
    ¬ ClassicalGroup.IsPSL X 2 q := by
  rintro ⟨F, _, _, _, ⟨e⟩⟩
  have he := (Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center (Matrix.SpecialLinearGroup (Fin 2) F))).symm.trans (Atlas.card_sl_two (F := F))
  rw [Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin,
    ← Nat.card_congr e.toEquiv] at he
  have hg : Nat.gcd 2 (Nat.card F - 1) ≤ 2 :=
    Nat.le_of_dvd (by decide) (Nat.gcd_dvd_left _ _)
  apply no_rankOne_order (Nat.card F) Finite.one_lt_card
  · rw [← he]
    exact dvd_mul_of_dvd_left hd _
  · rw [← he]
    exact (Nat.mul_le_mul hu hg).trans (by norm_num)

/-- The same interval excludes every SL₂ model, without a primality premise. -/
theorem no_sl_two_of_card {X : Type*} [Group X]
    (hd : 20160 ∣ Nat.card X) (hu : Nat.card X ≤ 80640) (q : ℕ) :
    ¬ IsSL X 2 q := by
  rintro ⟨F, _, _, _, ⟨e⟩⟩
  have he : Nat.card X = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv]
    exact Atlas.card_sl_two
  exact no_rankOne_order (Nat.card F) Finite.one_lt_card
    (he ▸ hd) ((he ▸ hu).trans (by norm_num))

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry.A312Specialization
