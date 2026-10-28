module

public import Theory.AtlasPort.Algebra.SplitOctonion.NormGeometry

/-!
# Concrete octonion identities for the Cayley sign change

The quadratic, polarized alternative, and middle Moufang identities below
are checked directly against Wilson's split-octonion multiplication table.
They imply the Cayley-frame multiplication rules used by `CayleyFlip`.
No associativity of the octonion algebra is assumed.

Coordinate source: the ATLAS port, Copyright (c) 2026 Gerald Höhn and the
ATLAS contributors, under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff, Wilson Eq. (4.11).
Application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(4), printed pp.3–4 and 481–482.
-/

@[expose] public section

open Atlas.SplitOctonion
namespace Atlas.G2.TernaryLocals.CharacterGeometry.CanonicalEight
variable {F : Type*} [Field F]

theorem flip_polar_unit (x : Carrier F) : normPolar unit x = trace x := by
  simp [normPolar, unit, trace]; ring

theorem flip_anticommutator (x y : Carrier F) :
    mul x y + mul y x = trace x • y + trace y • x - normPolar x y • unit := by
  ext i; fin_cases i <;> simp [mul, trace, normPolar, unit] <;> ring

theorem flip_left_polar (x y z : Carrier F) :
    mul x (mul y z) + mul y (mul x z) =
      trace x • mul y z + trace y • mul x z - normPolar x y • z := by
  ext i; fin_cases i <;> simp [mul, trace, normPolar] <;> ring

theorem flip_left_square (x y : Carrier F) :
    mul x (mul x y) = trace x • mul x y - norm x • y := by
  ext i; fin_cases i <;> simp [mul, trace, norm] <;> ring

theorem flip_right_square (x y : Carrier F) :
    mul (mul y x) x = trace x • mul y x - norm x • y := by
  ext i; fin_cases i <;> simp [mul, trace, norm] <;> ring

theorem flip_moufang (x y z : Carrier F) :
    mul (mul x y) (mul z x) = mul x (mul (mul y z) x) := by
  ext i; fin_cases i <;> simp [mul] <;> ring

theorem flip_skew (x y : Carrier F) (hx : trace x = 0) (hy : trace y = 0)
    (hxy : normPolar x y = 0) : mul x y = -mul y x := by
  apply eq_neg_of_add_eq_zero_left
  simpa [hx, hy, hxy] using flip_anticommutator x y

theorem flip_left_skew (x y z : Carrier F) (hx : trace x = 0) (hy : trace y = 0)
    (hxy : normPolar x y = 0) : mul x (mul y z) = -mul y (mul x z) := by
  apply eq_neg_of_add_eq_zero_left
  simpa [hx, hy, hxy] using flip_left_polar x y z

theorem flip_square (x : Carrier F) (hx : trace x = 0) :
    mul x x = -norm x • unit := by
  have h := quadratic_identity x
  simpa [hx, ← neg_smul] using eq_neg_of_add_eq_zero_left h
end Atlas.G2.TernaryLocals.CharacterGeometry.CanonicalEight
