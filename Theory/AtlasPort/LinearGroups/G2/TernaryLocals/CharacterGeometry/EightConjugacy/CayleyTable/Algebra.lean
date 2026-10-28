module

public import Theory.AtlasPort.Algebra.SplitOctonion.NormGeometry

/-!
# Octonion identities for Cayley frames

The polarized triple identity, square identities and middle Moufang identity
are proved directly from Wilson's split-octonion coordinates. These identities
hold over every field; no associative multiplication instance is used.
They supply the arbitrary-frame calculation in the parent Cayley-table module.

Coordinates and attribution: the licensed ATLAS split-octonion port, Wilson's
integral table, Eq. (4.11); see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. Application: Aschbacher–Smith,
*The Classification of Quasithin Groups*, Theorem 0.1.2(4).
-/

public section
namespace Atlas.G2.TernaryLocals.CharacterGeometry.EightConjugacy.CayleyTable
open Atlas.SplitOctonion
variable {F : Type*} [Field F]
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

private theorem pure_coord (x : Carrier F) (hx : trace x = 0) : x 4 = -x 3 := by
  exact eq_neg_of_add_eq_zero_right hx

/-- The polarized triple identity for imaginary octonions. -/
theorem pure_triple_identity (x y z : Carrier F)
    (hx : trace x = 0) (hy : trace y = 0) (hz : trace z = 0) :
    mul x (mul y z) + mul (mul x y) z =
      -(normPolar x y) • z + normPolar x z • y - normPolar y z • x -
      normPolar (mul x y) z • unit := by
  have hx' := pure_coord x hx
  have hy' := pure_coord y hy
  have hz' := pure_coord z hz
  ext i
  fin_cases i <;> simp [mul, normPolar, unit, hx', hy', hz'] <;> ring

theorem pure_mul_trace (x y : Carrier F) (hx : trace x = 0) (hy : trace y = 0) :
    trace (mul x y) = -normPolar x y := by
  simp [trace, mul, normPolar, pure_coord x hx, pure_coord y hy]
  ring

theorem pure_anticomm (x y : Carrier F) (hx : trace x = 0) (hy : trace y = 0)
    (hp : normPolar x y = 0) : mul x y = -mul y x := by
  have he : mul x y + mul y x = -normPolar x y • unit := by
    ext i
    fin_cases i <;> simp [mul, normPolar, unit, pure_coord x hx, pure_coord y hy] <;> ring
  rw [hp, neg_zero, zero_smul] at he
  exact eq_neg_of_add_eq_zero_left he

/-- Left multiplication by an imaginary vector squares to minus its norm. -/
theorem pure_left_square (x y : Carrier F) (hx : trace x = 0) :
    mul x (mul x y) = -(norm x) • y := by
  ext i
  fin_cases i <;> simp [mul, SplitOctonion.norm, pure_coord x hx] <;> ring

/-- Right multiplication by an imaginary vector squares to minus its norm. -/
theorem pure_right_square (x y : Carrier F) (hy : trace y = 0) :
    mul (mul x y) y = -(norm y) • x := by
  have hc : conjugate y = -y := by simp [conjugate, hy]
  have hi := mul_mul_conjugate_right x y
  rw [hc] at hi
  have hm : mul (mul x y) (-y) = -mul (mul x y) y := (multiplication (mul x y)).map_neg y
  rw [hm] at hi
  simpa using congrArg Neg.neg hi

/-- The middle Moufang identity, with the parentheses specified explicitly. -/
theorem moufang_middle (x y z : Carrier F) :
    mul (mul x y) (mul z x) = mul (mul x (mul y z)) x := by
  ext i
  fin_cases i <;> simp [mul] <;> ring

theorem trace_mul_identity (x y : Carrier F) :
    trace (mul x y) = trace x * trace y - normPolar x y := by
  simp [trace, mul, normPolar]
  ring

theorem trace_neg (x : Carrier F) : trace (-x) = -trace x := by simp [trace]; ring
theorem trace_smul (s : F) (x : Carrier F) : trace (s • x) = s * trace x := by
  simp [trace]; ring

theorem mul_neg_left (x y : Carrier F) : mul (-x) y = -mul x y := multiplication.map_neg₂ x y

theorem mul_neg_right (x y : Carrier F) : mul x (-y) = -mul x y := (multiplication x).map_neg y

/-- Imaginary factors with imaginary product anticommute, by conjugation. -/
theorem flip_of_pure (x y : Carrier F) (hx : trace x = 0) (hy : trace y = 0)
    (hxy : trace (mul x y) = 0) : mul y x = -mul x y := by
  have hc (z : Carrier F) (hz : trace z = 0) : conjugate z = -z := by simp [conjugate, hz]
  have he := conjugate_mul_reverse x y
  simpa only [hc _ hx, hc _ hy, hc _ hxy, mul_neg_left, mul_neg_right, neg_neg] using he.symm

theorem pure_square (x : Carrier F) (hx : trace x = 0) : mul x x = -norm x • unit := by
  have he := quadratic_identity x
  simpa only [hx, zero_smul, sub_zero, eq_neg_iff_add_eq_zero, neg_smul] using he

end Atlas.G2.TernaryLocals.CharacterGeometry.EightConjugacy.CayleyTable
