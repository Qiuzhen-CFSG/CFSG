/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechIntegralPairing.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechModTwo

/-!
Integral pairing and half-norm on the Leech lattice.
Dot-product divisibility makes integer division exact and yields the addition and doubling identities.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes

def leechIntegralPairing (x y : leech) : ℤ := integerDot x.val y.val / 8
def leechHalfNorm (x : leech) : ℤ := integerDot x.val x.val / 16

theorem leech_dot_divisible (x y : leech) : 8 ∣ integerDot x.val y.val := by
  apply integer_dual_divisible x.val ?_ y.val y.prop
  rw [leech_selfDual]
  exact Submodule.mem_map.mpr ⟨x.val,x.prop,rfl⟩

theorem leechIntegralPairing_mul (x y : leech) :
    8 * leechIntegralPairing x y = integerDot x.val y.val := by
  exact Int.mul_ediv_cancel' (leech_dot_divisible x y)

theorem leechHalfNorm_mul (x : leech) : 16 * leechHalfNorm x = integerDot x.val x.val := by
  exact Int.mul_ediv_cancel' (leech_norm_divisible x.val x.prop)

theorem leechIntegralPairing_comm (x y : leech) : leechIntegralPairing x y = leechIntegralPairing y x := by
  simp only [leechIntegralPairing,integerDot_comm]

theorem leechIntegralPairing_add_left (x y z : leech) :
    leechIntegralPairing (x+y) z = leechIntegralPairing x z + leechIntegralPairing y z := by
  have h := leechIntegralPairing_mul (x+y) z
  have hx := leechIntegralPairing_mul x z
  have hy := leechIntegralPairing_mul y z
  change 8 * leechIntegralPairing (x+y) z = integerDot (x.val+y.val) z.val at h
  rw [integerDot_add_left] at h
  omega

theorem leechIntegralPairing_add_right (x y z : leech) :
    leechIntegralPairing x (y+z) = leechIntegralPairing x y + leechIntegralPairing x z := by
  rw [leechIntegralPairing_comm x,leechIntegralPairing_add_left]
  rw [leechIntegralPairing_comm y,leechIntegralPairing_comm z]

theorem leechIntegralPairing_self (x : leech) : leechIntegralPairing x x = 2 * leechHalfNorm x := by
  have hx := leechIntegralPairing_mul x x
  have hy := leechHalfNorm_mul x
  omega

theorem leechHalfNorm_add (x y : leech) :
    leechHalfNorm (x+y) = leechHalfNorm x + leechHalfNorm y + leechIntegralPairing x y := by
  have h := leechHalfNorm_mul (x+y)
  have hx := leechHalfNorm_mul x
  have hy := leechHalfNorm_mul y
  have hb := leechIntegralPairing_mul x y
  change 16 * leechHalfNorm (x+y) = integerDot (x.val+y.val) (x.val+y.val) at h
  rw [integerDot_self_add] at h
  omega

theorem leechHalfNorm_double (x : leech) : leechHalfNorm ((2 : ℕ) • x) = 4 * leechHalfNorm x := by
  rw [two_nsmul,leechHalfNorm_add,leechIntegralPairing_self]
  ring

theorem leechIntegralPairing_double_left (x y : leech) :
    leechIntegralPairing ((2 : ℕ) • x) y = 2 * leechIntegralPairing x y := by
  rw [two_nsmul,leechIntegralPairing_add_left]
  ring

theorem leechIntegralPairing_double_right (x y : leech) :
    leechIntegralPairing x ((2 : ℕ) • y) = 2 * leechIntegralPairing x y := by
  rw [two_nsmul,leechIntegralPairing_add_right]
  ring

theorem leechIntegralPairing_rational (x y : leech) :
    (leechIntegralPairing x y : ℚ) = rationalForm (rationalEmbedding x.val) (rationalEmbedding y.val) := by
  rw [rationalForm_integer,← leechIntegralPairing_mul]
  push_cast
  ring

end Atlas.Lattices
