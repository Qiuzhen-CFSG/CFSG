module

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry

/-!
# Binary norm calculations for the canonical ternary lines

Multiplication by a nonisotropic octonion is a similarity for the polar form.
For an orthogonal ternary binary plane, the norm-one vectors when both axes
have norm one, and the nonisotropic vectors when the two axis norms are
opposite, lie precisely on the two axes. The coefficient calculations are
checked by kernel reduction over F₃; no binary-form classification is assumed.

These lemmas support the norm-line construction above four-groups in G₂(3).
Coordinates use the licensed ATLAS split-octonion port; see LICENSES/ATLAS.txt
and LICENSES/ATLAS-CITATION.cff. Application: Aschbacher–Smith,
*The Classification of Quasithin Groups*, Theorem 0.1.2(4).
-/

@[expose] public section

namespace Atlas.G2.TernaryLocals.CharacterGeometry.CanonicalEight
open Atlas.SplitOctonion

theorem normPolar_mul_right (x y v : V) :
    normPolar (mul x v) (mul y v) = norm v * normPolar x y := by
  rw [normPolar_eq, ← SplitOctonion.add_mul, norm_mul, norm_mul, norm_mul, normPolar_eq]
  ring

theorem normPolar_mul_left (v x y : V) :
    normPolar (mul v x) (mul v y) = norm v * normPolar x y := by
  rw [normPolar_eq, ← SplitOctonion.mul_add, norm_mul, norm_mul, norm_mul, normPolar_eq]
  ring

theorem norm_orthogonal_sum (x y : V) (hxy : normPolar x y = 0) (r s : ZMod 3) :
    norm (r • x + s • y) = r^2 * norm x + s^2 * norm y := by
  rw [norm_add, norm_smul, norm_smul]
  simp only [map_smul, LinearMap.smul_apply, hxy, smul_zero, add_zero]

theorem norm_one_iff_axis (x y : V) (hxy : normPolar x y = 0)
    (hx : norm x = 1) (hy : norm y = 1) (r s : ZMod 3) :
    norm (r • x + s • y) = 1 ↔ (r ≠ 0 ∧ s = 0) ∨ (r = 0 ∧ s ≠ 0) := by
  rw [norm_orthogonal_sum x y hxy, hx, hy, mul_one, mul_one]
  exact (by decide +kernel : ∀ r s : ZMod 3,
    r^2 + s^2 = 1 ↔ (r ≠ 0 ∧ s = 0) ∨ (r = 0 ∧ s ≠ 0)) r s

theorem norm_ne_zero_iff_axis (x y : V) (hxy : normPolar x y = 0)
    (hx : norm x ≠ 0) (hy : norm y = -norm x) (r s : ZMod 3) :
    norm (r • x + s • y) ≠ 0 ↔ (r ≠ 0 ∧ s = 0) ∨ (r = 0 ∧ s ≠ 0) := by
  rw [norm_orthogonal_sum x y hxy, hy]
  exact (by decide +kernel : ∀ n r s : ZMod 3, n ≠ 0 →
    (r^2 * n + s^2 * (-n) ≠ 0 ↔ (r ≠ 0 ∧ s = 0) ∨ (r = 0 ∧ s ≠ 0))) (norm x) r s hx

end Atlas.G2.TernaryLocals.CharacterGeometry.CanonicalEight
