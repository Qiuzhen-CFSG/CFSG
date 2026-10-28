/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechShortClassBounds.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Proof syntax and simplifier arguments are adjusted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechModTwoAction

/-!
Bounds on short vectors in a fixed class modulo twice the Leech lattice.
The minimum applied to half-sums and half-differences gives uniqueness or orthogonality.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes

theorem leechHalfNorm_nonneg (x : leech) : 0 ≤ leechHalfNorm x := by
  have h := leechHalfNorm_mul x
  have hn := integerDot_self_nonneg x.val
  omega

theorem leechHalfNorm_min (x : leech) (hx : x ≠ 0) : 2 ≤ leechHalfNorm x := by
  have hv : x.val ≠ 0 := by intro h; apply hx; exact Subtype.ext h
  have h := leech_raw_minimum x.val x.prop hv
  have he := leechHalfNorm_mul x
  omega

theorem leechHalfNorm_neg (x : leech) : leechHalfNorm (-x) = leechHalfNorm x := by
  simp [leechHalfNorm,integerDot]

theorem leechHalfNorm_halves (y z : leech) :
    leechHalfNorm (y + (2 : ℕ) • z) + leechHalfNorm y =
      2 * (leechHalfNorm z + leechHalfNorm (y+z)) := by
  rw [leechHalfNorm_add,leechHalfNorm_double,leechIntegralPairing_double_right,leechHalfNorm_add]
  ring

theorem leech_congruent_short_bound (x y : leech) (hc : leechReduction x = leechReduction y)
    (he : x ≠ y) (hn : x ≠ -y) : 8 ≤ leechHalfNorm x + leechHalfNorm y := by
  obtain ⟨z,hz⟩ := (leechReduction_eq_iff x y).mp hc
  have hz0 : z ≠ 0 := by intro h; apply he; simpa [h] using hz
  have hw0 : y+z ≠ 0 := by
    intro h
    apply hn
    rw [hz,two_nsmul]
    have hz' : z = -y := eq_neg_of_add_eq_zero_right h
    rw [hz']; abel
  have hb := leechHalfNorm_halves y z
  rw [← hz] at hb
  have hzmin := leechHalfNorm_min z hz0
  have hwmin := leechHalfNorm_min (y+z) hw0
  omega

theorem leech_congruent_short_unique (x y : leech)
    (hc : leechReduction x = leechReduction y) (hn : leechHalfNorm x + leechHalfNorm y < 8) :
    x = y ∨ x = -y := by
  by_contra h
  push Not at h
  have hb := leech_congruent_short_bound x y hc h.1 h.2
  omega

theorem leech_different_short_classes (x y : leech)
    (hn : leechHalfNorm x + leechHalfNorm y < 8) (hne : leechHalfNorm x ≠ leechHalfNorm y) :
    leechReduction x ≠ leechReduction y := by
  intro hc
  rcases leech_congruent_short_unique x y hc hn with h | h
  · exact hne (congrArg leechHalfNorm h)
  · apply hne
    rw [h,leechHalfNorm_neg]

theorem leech_zero_class_min (x : leech) (hx : x ≠ 0) (hc : leechReduction x = 0) :
    8 ≤ leechHalfNorm x := by
  obtain ⟨z,hz⟩ := (leechReduction_eq_zero x).mp hc
  have hz0 : z ≠ 0 := by intro h; apply hx; rw [← hz,h]; simp
  have hmin := leechHalfNorm_min z hz0
  rw [← hz,leechHalfNorm_double]
  omega

theorem leech_norm_eight_congruent_orthogonal (x y : leech)
    (hx : leechHalfNorm x = 4) (hy : leechHalfNorm y = 4)
    (hc : leechReduction x = leechReduction y) (he : x ≠ y) (hn : x ≠ -y) :
    leechIntegralPairing x y = 0 := by
  obtain ⟨z,hz⟩ := (leechReduction_eq_iff x y).mp hc
  have hz0 : z ≠ 0 := by intro h; apply he; simpa [h] using hz
  have hw0 : y+z ≠ 0 := by
    intro h
    apply hn
    rw [hz,two_nsmul]
    have hz' : z = -y := eq_neg_of_add_eq_zero_right h
    rw [hz']; abel
  have hmin := leechHalfNorm_min z hz0
  have hwmin := leechHalfNorm_min (y+z) hw0
  have hb := leechHalfNorm_halves y z
  rw [← hz,hx,hy] at hb
  have hz2 : leechHalfNorm z = 2 := by omega
  have hw2 : leechHalfNorm (y+z) = 2 := by omega
  have hpair := leechHalfNorm_add y z
  rw [hy,hz2,hw2] at hpair
  rw [hz,leechIntegralPairing_add_left,leechIntegralPairing_self,
    leechIntegralPairing_double_left,leechIntegralPairing_comm z,hy]
  omega

theorem leech_shell_halfNorm (r : ℤ) (x : LeechShell r) : 2 * leechHalfNorm x.val = r := by
  have h := leechHalfNorm_mul x.val
  rw [x.prop] at h
  omega

theorem leech_short_shell_class_nonzero (r : ℤ) (hr : 0 < r ∧ r ≤ 8) (x : LeechShell r) :
    leechReduction x.val ≠ 0 := by
  intro hc
  have hx : x.val ≠ 0 := by
    intro h
    have hn := x.prop
    rw [h] at hn
    simp [integerDot] at hn
    omega
  have h := leech_zero_class_min x.val hx hc
  have hn := leech_shell_halfNorm r x
  omega

end Atlas.Lattices
