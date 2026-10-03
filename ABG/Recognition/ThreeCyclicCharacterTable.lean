module
public import ABG.Recognition.ThreeCharacterTable
/-!
# The GL₂(3) cyclic character sections

An explicit primitive eighth root fixes the orientation of the two faithful
rows. The eight powers of the rotation are conjugate to the concrete table
representatives; evaluation and reduction modulo eight give the cyclic
section formulas in the ABG row order.

Source: Alperin--Brauer--Gorenstein III.2 Proposition 2 and III.6;
Wong (1964), Table 1. The root is chosen so that its first and third powers
sum to the negative of Wong's chosen square root of minus two.
-/

open Matrix Matrix.GeneralLinearGroup BenderGlauberman
namespace ABG
noncomputable section
local notation "L" => GL (Fin 2) (ZMod 3)

/-- The primitive eighth root compatible with the faithful GL₂(3) table. -/
@[expose] public def glTwoThreeSectionRoot : ℂ := -glTwoThreeOmega * (1 - Complex.I) / 2

private theorem sectionRoot_sq : glTwoThreeSectionRoot ^ 2 = Complex.I := by
  calc
    _ = glTwoThreeOmega ^ 2 * (1 - 2 * Complex.I + Complex.I ^ 2) / 4 := by
      unfold glTwoThreeSectionRoot
      ring
    _ = _ := by rw [glTwoThreeOmega_sq, Complex.I_sq]; ring

private theorem sectionRoot_four : glTwoThreeSectionRoot ^ 4 = -1 := by
  calc _ = (glTwoThreeSectionRoot ^ 2) ^ 2 := by ring
       _ = -1 := by rw [sectionRoot_sq, Complex.I_sq]

private theorem sectionRoot_eight : glTwoThreeSectionRoot ^ 8 = 1 := by
  calc _ = (glTwoThreeSectionRoot ^ 4) ^ 2 := by ring
       _ = 1 := by rw [sectionRoot_four]; norm_num

public theorem glTwoThreeSectionRoot_primitive : IsPrimitiveRoot glTwoThreeSectionRoot 8 := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide : 0 < 8) sectionRoot_eight
  intro p hp hpd
  have hp2 : p = 2 := by
    have hd : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 from hpd)
    exact (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hp.ne_one
  subst p
  norm_num only [Nat.reduceDiv]
  rw [sectionRoot_four]
  norm_num

private theorem sectionRoot_ne_zero : glTwoThreeSectionRoot ≠ 0 := by
  intro h
  simpa [h] using sectionRoot_eight

private theorem sectionRoot_omega :
    glTwoThreeSectionRoot + glTwoThreeSectionRoot ^ 3 = -glTwoThreeOmega := by
  rw [pow_succ _ 2, sectionRoot_sq]
  unfold glTwoThreeSectionRoot
  calc _ = -glTwoThreeOmega * (1 - Complex.I^2) / 2 := by ring
       _ = _ := by rw [Complex.I_sq]; ring


private theorem complex_zpow_mod_eight {z : ℂ} (hz : z ^ 8 = 1) (h : ℤ) :
    z ^ h = z ^ (h % 8) := by
  have hn : z ≠ 0 := by intro he; norm_num [he] at hz
  have hu : (Units.mk0 z hn) ^ (8 : ℤ) = 1 := by
    apply Units.ext
    simpa using hz
  simpa only [Units.val_zpow_eq_zpow_val, Units.val_mk0] using
    congrArg (fun u : ℂˣ => (u : ℂ)) (zpow_eq_zpow_emod h hu)

private theorem neg_sectionRoot_eight : (-glTwoThreeSectionRoot) ^ 8 = 1 := by
  simpa only [neg_pow, show (-1 : ℂ)^8 = 1 by norm_num, one_mul] using sectionRoot_eight

private theorem rotation_powers (n : Fin 8) :
    IsConj (threeRotation ^ n.val) (threeClassRepr (![0,6,2,6,1,7,2,7] n)) := by
  let g : L := mkOfDetNeZero !![(0 : ZMod 3),1;2,0] (by decide)
  have hc : ∀ n : Fin 8, ∃ g : L,
      g * threeRotation ^ n.val = threeClassRepr (![0,6,2,6,1,7,2,7] n) * g := by
    intro n
    fin_cases n
    all_goals first
      | exact ⟨1, by decide +kernel⟩
      | exact ⟨g, by decide +kernel⟩
  obtain ⟨b, hb⟩ := hc n
  exact isConj_iff.mpr ⟨b, by rw [hb, mul_assoc, mul_inv_cancel, mul_one]⟩

/-- The concrete cyclic section, in the ABG row order. -/
public theorem glTwoThree_cyclic_section (h : ℤ) (hh : ¬ 4 ∣ h) (j : Fin 8) :
    glTwoThreeCharacter (![0,4,3,1,5,2,6,7] j) (threeRotation ^ h) =
      ![1,-1,-((-1 : ℂ)^h),(-1 : ℂ)^h,0,
        -(glTwoThreeSectionRoot^(2*h) + (-glTwoThreeSectionRoot)^(-(2*h))),
        -(glTwoThreeSectionRoot^h + (-glTwoThreeSectionRoot)^(-h)),
        -(glTwoThreeSectionRoot^(-h) + (-glTwoThreeSectionRoot)^h)] j := by
  have hr : orderOf threeRotation = 8 := three_conjugacy_data.2.1 6
  have hp (z : ℂ) (hz : z ^ 8 = 1) (a b : ℤ) (hab : a % 8 = b % 8) : z^a = z^b := by
    rw [complex_zpow_mod_eight hz a, complex_zpow_mod_eight hz b, hab]
  have hpow : threeRotation ^ h = threeRotation ^ (h % 8) := by
    simpa only [hr, Nat.cast_ofNat] using (zpow_mod_orderOf threeRotation h).symm
  rw [hpow,
    hp (-1) (by norm_num) h (h%8) (by omega),
    hp glTwoThreeSectionRoot sectionRoot_eight (2*h) (2*(h%8)) (by omega),
    hp (-glTwoThreeSectionRoot) neg_sectionRoot_eight (-(2*h)) (-(2*(h%8))) (by omega),
    hp glTwoThreeSectionRoot sectionRoot_eight h (h%8) (by omega),
    hp (-glTwoThreeSectionRoot) neg_sectionRoot_eight (-h) (-(h%8)) (by omega),
    hp glTwoThreeSectionRoot sectionRoot_eight (-h) (-(h%8)) (by omega),
    hp (-glTwoThreeSectionRoot) neg_sectionRoot_eight h (h%8) (by omega)]
  have hmod : h % 8 = 1 ∨ h % 8 = 2 ∨ h % 8 = 3 ∨
      h % 8 = 5 ∨ h % 8 = 6 ∨ h % 8 = 7 := by omega
  have hv (n : ℕ) (hn : n < 8) (i : Fin 8) :
      glTwoThreeCharacter i (threeRotation ^ n) =
        glTwoThreeCharacterTable i (![0,6,2,6,1,7,2,7] ⟨n, hn⟩) := by
    obtain ⟨g, hg⟩ := isConj_iff.mp (rotation_powers ⟨n, hn⟩)
    rw [← glTwoThreeCharacter_values, ← hg]
    exact (irreducibleCharacter_isClassFunction (glTwoThreeCharacter_irreducible i) _ g).symm
  have hz6 : glTwoThreeSectionRoot^6 = -Complex.I := by
    calc _ = glTwoThreeSectionRoot^4 * glTwoThreeSectionRoot^2 := by ring
         _ = _ := by rw [sectionRoot_four, sectionRoot_sq]; ring
  have hz5 : glTwoThreeSectionRoot^5 = -glTwoThreeSectionRoot := by
    rw [pow_succ, sectionRoot_four]; ring
  have hz7 : glTwoThreeSectionRoot^7 = -glTwoThreeSectionRoot^3 := by
    calc _ = glTwoThreeSectionRoot^4 * glTwoThreeSectionRoot^3 := by ring
         _ = _ := by rw [sectionRoot_four]; ring
  have hz10 : glTwoThreeSectionRoot^10 = Complex.I := by
    calc _ = glTwoThreeSectionRoot^8 * glTwoThreeSectionRoot^2 := by ring
         _ = _ := by rw [sectionRoot_eight, sectionRoot_sq]; ring
  have hz12 : glTwoThreeSectionRoot^12 = -1 := by
    calc _ = glTwoThreeSectionRoot^8 * glTwoThreeSectionRoot^4 := by ring
         _ = _ := by rw [sectionRoot_eight, sectionRoot_four]; ring
  have hz14 : glTwoThreeSectionRoot^14 = -Complex.I := by
    calc _ = glTwoThreeSectionRoot^8 * glTwoThreeSectionRoot^6 := by ring
         _ = _ := by rw [sectionRoot_eight, hz6]; ring
  rcases hmod with hm | hm | hm | hm | hm | hm <;> rw [hm]
  all_goals norm_num only [zpow_ofNat, Int.reduceMul, Int.reduceNeg]
  all_goals
    simp only [complex_zpow_mod_eight neg_sectionRoot_eight (-2),
      complex_zpow_mod_eight neg_sectionRoot_eight (-4),
      complex_zpow_mod_eight neg_sectionRoot_eight (-6),
      complex_zpow_mod_eight neg_sectionRoot_eight (-10),
      complex_zpow_mod_eight neg_sectionRoot_eight (-12),
      complex_zpow_mod_eight neg_sectionRoot_eight (-14),
      complex_zpow_mod_eight neg_sectionRoot_eight (-1),
      complex_zpow_mod_eight neg_sectionRoot_eight (-3),
      complex_zpow_mod_eight neg_sectionRoot_eight (-5),
      complex_zpow_mod_eight neg_sectionRoot_eight (-7),
      complex_zpow_mod_eight sectionRoot_eight (-1),
      complex_zpow_mod_eight sectionRoot_eight (-2),
      complex_zpow_mod_eight sectionRoot_eight (-3),
      complex_zpow_mod_eight sectionRoot_eight (-5),
      complex_zpow_mod_eight sectionRoot_eight (-6),
      complex_zpow_mod_eight sectionRoot_eight (-7)]
  all_goals norm_num only [Int.reduceMod, zpow_ofNat]
  · rw [hv 1 (by decide)]
    fin_cases j
    · change (1 : ℂ) = 1
      rfl
    · change (-1 : ℂ) = -1
      rfl
    · change (1 : ℂ) = 1
      rfl
    · change (-1 : ℂ) = -1
      rfl
    · change (0 : ℂ) = 0
      rfl
    · change (0 : ℂ) = -(glTwoThreeSectionRoot^2 + (-glTwoThreeSectionRoot)^6)
      norm_num [neg_pow, sectionRoot_sq, sectionRoot_four, hz5, hz6, hz7, hz10, hz12, hz14]
    · change (glTwoThreeOmega : ℂ) = -(glTwoThreeSectionRoot^1 + (-glTwoThreeSectionRoot)^7)
      norm_num [neg_pow, sectionRoot_sq, sectionRoot_four, hz5, hz6, hz7, hz10, hz12, hz14]
      linear_combination sectionRoot_omega
    · change (-glTwoThreeOmega : ℂ) = -(glTwoThreeSectionRoot^7 + (-glTwoThreeSectionRoot)^1)
      norm_num [neg_pow, sectionRoot_sq, sectionRoot_four, hz5, hz6, hz7, hz10, hz12, hz14]
      linear_combination -sectionRoot_omega
  · rw [hv 2 (by decide)]
    fin_cases j
    · change (1 : ℂ) = 1
      rfl
    · change (-1 : ℂ) = -1
      rfl
    · change (-1 : ℂ) = -1
      rfl
    · change (1 : ℂ) = 1
      rfl
    · change (0 : ℂ) = 0
      rfl
    · change (2 : ℂ) = -(glTwoThreeSectionRoot^4 + (-glTwoThreeSectionRoot)^4)
      norm_num [neg_pow, sectionRoot_sq, sectionRoot_four, hz5, hz6, hz7, hz10, hz12, hz14]
    · change (0 : ℂ) = -(glTwoThreeSectionRoot^2 + (-glTwoThreeSectionRoot)^6)
      norm_num [neg_pow, sectionRoot_sq, sectionRoot_four, hz5, hz6, hz7, hz10, hz12, hz14]
    · change (0 : ℂ) = -(glTwoThreeSectionRoot^6 + (-glTwoThreeSectionRoot)^2)
      norm_num [neg_pow, sectionRoot_sq, sectionRoot_four, hz5, hz6, hz7, hz10, hz12, hz14]
  · rw [hv 3 (by decide)]
    fin_cases j
    · change (1 : ℂ) = 1
      rfl
    · change (-1 : ℂ) = -1
      rfl
    · change (1 : ℂ) = 1
      rfl
    · change (-1 : ℂ) = -1
      rfl
    · change (0 : ℂ) = 0
      rfl
    · change (0 : ℂ) = -(glTwoThreeSectionRoot^6 + (-glTwoThreeSectionRoot)^2)
      norm_num [neg_pow, sectionRoot_sq, sectionRoot_four, hz5, hz6, hz7, hz10, hz12, hz14]
    · change (glTwoThreeOmega : ℂ) = -(glTwoThreeSectionRoot^3 + (-glTwoThreeSectionRoot)^5)
      norm_num [neg_pow, sectionRoot_sq, sectionRoot_four, hz5, hz6, hz7, hz10, hz12, hz14]
      linear_combination sectionRoot_omega
    · change (-glTwoThreeOmega : ℂ) = -(glTwoThreeSectionRoot^5 + (-glTwoThreeSectionRoot)^3)
      norm_num [neg_pow, sectionRoot_sq, sectionRoot_four, hz5, hz6, hz7, hz10, hz12, hz14]
      linear_combination -sectionRoot_omega
  · rw [hv 5 (by decide)]
    fin_cases j
    · change (1 : ℂ) = 1
      rfl
    · change (-1 : ℂ) = -1
      rfl
    · change (1 : ℂ) = 1
      rfl
    · change (-1 : ℂ) = -1
      rfl
    · change (0 : ℂ) = 0
      rfl
    · change (0 : ℂ) = -(glTwoThreeSectionRoot^10 + (-glTwoThreeSectionRoot)^6)
      norm_num [neg_pow, sectionRoot_sq, sectionRoot_four, hz5, hz6, hz7, hz10, hz12, hz14]
    · change (-glTwoThreeOmega : ℂ) = -(glTwoThreeSectionRoot^5 + (-glTwoThreeSectionRoot)^3)
      norm_num [neg_pow, sectionRoot_sq, sectionRoot_four, hz5, hz6, hz7, hz10, hz12, hz14]
      linear_combination -sectionRoot_omega
    · change (glTwoThreeOmega : ℂ) = -(glTwoThreeSectionRoot^3 + (-glTwoThreeSectionRoot)^5)
      norm_num [neg_pow, sectionRoot_sq, sectionRoot_four, hz5, hz6, hz7, hz10, hz12, hz14]
      linear_combination sectionRoot_omega
  · rw [hv 6 (by decide)]
    fin_cases j
    · change (1 : ℂ) = 1
      rfl
    · change (-1 : ℂ) = -1
      rfl
    · change (-1 : ℂ) = -1
      rfl
    · change (1 : ℂ) = 1
      rfl
    · change (0 : ℂ) = 0
      rfl
    · change (2 : ℂ) = -(glTwoThreeSectionRoot^12 + (-glTwoThreeSectionRoot)^4)
      norm_num [neg_pow, sectionRoot_sq, sectionRoot_four, hz5, hz6, hz7, hz10, hz12, hz14]
    · change (0 : ℂ) = -(glTwoThreeSectionRoot^6 + (-glTwoThreeSectionRoot)^2)
      norm_num [neg_pow, sectionRoot_sq, sectionRoot_four, hz5, hz6, hz7, hz10, hz12, hz14]
    · change (0 : ℂ) = -(glTwoThreeSectionRoot^2 + (-glTwoThreeSectionRoot)^6)
      norm_num [neg_pow, sectionRoot_sq, sectionRoot_four, hz5, hz6, hz7, hz10, hz12, hz14]
  · rw [hv 7 (by decide)]
    fin_cases j
    · change (1 : ℂ) = 1
      rfl
    · change (-1 : ℂ) = -1
      rfl
    · change (1 : ℂ) = 1
      rfl
    · change (-1 : ℂ) = -1
      rfl
    · change (0 : ℂ) = 0
      rfl
    · change (0 : ℂ) = -(glTwoThreeSectionRoot^14 + (-glTwoThreeSectionRoot)^2)
      norm_num [neg_pow, sectionRoot_sq, sectionRoot_four, hz5, hz6, hz7, hz10, hz12, hz14]
    · change (-glTwoThreeOmega : ℂ) = -(glTwoThreeSectionRoot^7 + (-glTwoThreeSectionRoot)^1)
      norm_num [neg_pow, sectionRoot_sq, sectionRoot_four, hz5, hz6, hz7, hz10, hz12, hz14]
      linear_combination -sectionRoot_omega
    · change (glTwoThreeOmega : ℂ) = -(glTwoThreeSectionRoot^1 + (-glTwoThreeSectionRoot)^7)
      norm_num [neg_pow, sectionRoot_sq, sectionRoot_four, hz5, hz6, hz7, hz10, hz12, hz14]
      linear_combination sectionRoot_omega

end
end ABG
