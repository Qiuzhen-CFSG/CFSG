module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.SourceWords

/-! The ten defining correction equations, as equations in the actual center.
The factor ordering is normalized using commutative group algebra. -/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
open scoped IsMulCommutative

theorem correctionEquation0 : (normalizedRelatorError .i_r1) ^ (-2 : ℤ) * (normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .iii_s1_s8 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * normalizedRelatorError .vi_s1_r1 * (normalizedRelatorError .vii_s5) ^ (2 : ℤ) * normalizedRelatorError .viii_s7 = 1 := by
  have h : (normalizedRelatorError .i_r1) ^ (-2 : ℤ) * (normalizedRelatorError .i_r8) ^ (-1 : ℤ) * normalizedRelatorError .iii_s1_s8 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * normalizedRelatorError .vi_s1_r1 * (normalizedRelatorError .vii_s5) ^ (2 : ℤ) * normalizedRelatorError .viii_s7 = 1 := by
    apply Subtype.ext
    simpa [normalizedRelatorError, correctionWord] using normalizedGenerator_correctionWord .r1
  exact h

theorem correctionEquation1 : (normalizedRelatorError .i_r1) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ) * normalizedRelatorError .vi_r8_s8 * (normalizedRelatorError .vii_s2) ^ (3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) = 1 := by
  have h : (normalizedRelatorError .i_r1) ^ (-3 : ℤ) * (normalizedRelatorError .iii_s1_s7) ^ (3 : ℤ) * (normalizedRelatorError .v_s7_s4) ^ (-3 : ℤ) * normalizedRelatorError .vi_r8_s8 * (normalizedRelatorError .vii_s2) ^ (3 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) = 1 := by
    apply Subtype.ext
    simpa [normalizedRelatorError, correctionWord] using normalizedGenerator_correctionWord .r8
  exact h

theorem correctionEquation2 : (normalizedRelatorError .iii_s1_s8) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) = 1 := by
  have h : (normalizedRelatorError .iii_s1_s8) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4 * normalizedRelatorError .viii_s4 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) = 1 := by
    apply Subtype.ext
    simpa [normalizedRelatorError, correctionWord] using normalizedGenerator_correctionWord .s1
  exact h

theorem correctionEquation3 : (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * normalizedRelatorError .v_s7_s4 = 1 := by
  have h : (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * normalizedRelatorError .v_s7_s4 = 1 := by
    apply Subtype.ext
    simpa [normalizedRelatorError, correctionWord] using normalizedGenerator_correctionWord .s2
  exact h

theorem correctionEquation4 : (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .vii_s3) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3 = 1 := by
  have h : (normalizedRelatorError .i_s1) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4 * (normalizedRelatorError .vii_s3) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s4) ^ (-1 : ℤ) * normalizedRelatorError .viii_s3 = 1 := by
    apply Subtype.ext
    simpa [normalizedRelatorError, correctionWord] using normalizedGenerator_correctionWord .s3
  exact h

theorem correctionEquation5 : (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) = 1 := by
  have h : (normalizedRelatorError .iv_s7_s2) ^ (-1 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) = 1 := by
    apply Subtype.ext
    simpa [normalizedRelatorError, correctionWord] using normalizedGenerator_correctionWord .s4
  exact h

theorem correctionEquation6 : normalizedRelatorError .iii_s1_s8 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .vii_s5) ^ (-2 : ℤ) * normalizedRelatorError .vii_s3 * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) = 1 := by
  have h : normalizedRelatorError .iii_s1_s8 * (normalizedRelatorError .v_s5_s4) ^ (-1 : ℤ) * (normalizedRelatorError .vii_s5) ^ (-2 : ℤ) * normalizedRelatorError .vii_s3 * (normalizedRelatorError .viii_s4) ^ (2 : ℤ) * (normalizedRelatorError .viii_s1) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) = 1 := by
    apply Subtype.ext
    simpa [normalizedRelatorError, correctionWord] using normalizedGenerator_correctionWord .s5
  exact h

theorem correctionEquation7 : (normalizedRelatorError .iv_s2_s8) ^ (-1 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4 = 1 := by
  have h : (normalizedRelatorError .iv_s2_s8) ^ (-1 : ℤ) * normalizedRelatorError .iv_s7_s2 * (normalizedRelatorError .v_s7_s4) ^ (-1 : ℤ) * normalizedRelatorError .v_s5_s4 = 1 := by
    apply Subtype.ext
    simpa [normalizedRelatorError, correctionWord] using normalizedGenerator_correctionWord .s6
  exact h

theorem correctionEquation8 : (normalizedRelatorError .i_r1) ^ (2 : ℤ) * (normalizedRelatorError .vii_r3) ^ (-2 : ℤ) * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3 = 1 := by
  have h : (normalizedRelatorError .i_r1) ^ (2 : ℤ) * (normalizedRelatorError .vii_r3) ^ (-2 : ℤ) * normalizedRelatorError .viii_s1 * (normalizedRelatorError .viii_s7) ^ (-1 : ℤ) * (normalizedRelatorError .viii_s3) ^ (-1 : ℤ) * normalizedRelatorError .viii_r3 = 1 := by
    apply Subtype.ext
    simpa [normalizedRelatorError, correctionWord] using normalizedGenerator_correctionWord .s7
  exact h

theorem correctionEquation9 : normalizedRelatorError .i_r1 * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .vii_s2) ^ (-1 : ℤ) = 1 := by
  have h : normalizedRelatorError .i_r1 * (normalizedRelatorError .iii_s1_s7) ^ (-1 : ℤ) * normalizedRelatorError .v_s7_s4 * (normalizedRelatorError .vii_s2) ^ (-1 : ℤ) = 1 := by
    apply Subtype.ext
    simpa [normalizedRelatorError, correctionWord] using normalizedGenerator_correctionWord .s8
  exact h

theorem central_mul_one {a b : C} (ha : a = 1) (hb : b = 1) : a * b = 1 := by
  rw [ha, hb, mul_one]

theorem central_zpow_one {a : C} (ha : a = 1) (n : ℤ) : a ^ n = 1 := by
  rw [ha, one_zpow]

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
