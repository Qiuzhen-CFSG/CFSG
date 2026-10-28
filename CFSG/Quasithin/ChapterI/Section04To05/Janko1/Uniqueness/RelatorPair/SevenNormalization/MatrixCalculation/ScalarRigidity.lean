module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.MatrixCalculation.LinearShape
import Mathlib.Tactic.Ring

/-!
# The power relations determine Janko's second matrix

The linear normalizer equations leave three entries a,b,c. The (0,0) and
(0,1) entries of W² = I give two quadratic equations. The (0,0) entry of
(XW)⁵ = I gives a fifth-degree equation. Exhaustion of the three scalars
in F₁₁, checked by the kernel, leaves only (3,9,1). This is a scalar
certificate, not an enumeration of all seven-dimensional matrices.

The fifth-degree formula is proved symbolically using the displayed square
of XW. Thus no external computation supplies an unproved matrix identity.
The calculation completes the coordinate-dependent step of Gorenstein,
*Finite Groups*, §16.6, (6.1)–(6.2), pp.482–483.
-/

namespace CFSG.Quasithin.Janko1RelatorPair.SevenNormalization.MatrixCalculation

private abbrev Mat := Matrix (Fin 7) (Fin 7) (ZMod 11)

private def fifthEntry (a b c : ZMod 11) : ZMod 11 :=
  -9*a^5 - 3*a^4*b - 29*a^4*c + 2*a^3*b^2 + 32*a^3*b*c + 14*a^3*c^2 +
  9*a^2*b^3 - 11*a^2*b^2*c + 23*a^2*b*c^2 - 29*a^2*c^3 - 3*a*b^4 -
  6*a*b^3*c + 14*a*b*c^3 + 11*a*c^4 + 2*b^4*c - 13*b^3*c^2 - b^2*c^3 +
  5*b*c^4 - 9*c^5

private def square (a b c : ZMod 11) : Mat :=
  !![a^2 - b^2 + c^2, -a^2 + a*b + a*c - b*c + c^2, a^2 - a*b + a*c - b*c + c^2, a^2 - a*b + a*c - b*c + c^2, a^2 + a*b + a*c - b*c - c^2, -a^2 - a*b + 3*a*c + b*c - c^2, a^2 - a*b - a*c + b*c + c^2;
     a^2 - a*b - a*c + b*c - c^2, a^2 - b^2 - c^2, a^2 + a*b - 3*a*c - b*c + c^2, -a^2 + a*b + a*c - b*c - c^2, -a^2 - a*b + a*c - b*c + c^2, a^2 - a*b + a*c - b*c - c^2, a^2 - a*b + a*c - b*c - c^2;
     a^2 - a*b + a*c - b*c + c^2, -a^2 - a*b + 3*a*c + b*c - c^2, a^2 - b^2 + c^2, a^2 - a*b + a*c - b*c + c^2, a^2 + a*b + a*c - b*c - c^2, a^2 - a*b - a*c + b*c + c^2, -a^2 + a*b + a*c - b*c + c^2;
     a^2 - a*b + a*c - b*c + c^2, a^2 - a*b - a*c + b*c + c^2, a^2 - a*b + a*c - b*c + c^2, a^2 - b^2 + c^2, a^2 + a*b + a*c - b*c - c^2, -a^2 + a*b + a*c - b*c + c^2, -a^2 - a*b + 3*a*c + b*c - c^2;
     a^2 + a*b + a*c - b*c - c^2, a^2 + a*b - a*c + b*c - c^2, a^2 + a*b + a*c - b*c - c^2, a^2 + a*b + a*c - b*c - c^2, 3*a^2 + b^2 - 3*c^2, a^2 + a*b - a*c + b*c - c^2, a^2 + a*b - a*c + b*c - c^2;
     a^2 + a*b - 3*a*c - b*c + c^2, a^2 - a*b + a*c - b*c - c^2, -a^2 + a*b + a*c - b*c - c^2, a^2 - a*b - a*c + b*c - c^2, -a^2 - a*b + a*c - b*c + c^2, a^2 - b^2 - c^2, a^2 - a*b + a*c - b*c - c^2;
     -a^2 + a*b + a*c - b*c - c^2, a^2 - a*b + a*c - b*c - c^2, a^2 - a*b - a*c + b*c - c^2, a^2 + a*b - 3*a*c - b*c + c^2, -a^2 - a*b + a*c - b*c + c^2, a^2 - a*b + a*c - b*c - c^2, a^2 - b^2 - c^2]

private def product (a b c : ZMod 11) : Mat :=
  !![-a,-b,-c,-c,-a,-c,-a;
      b,c,c,a,c,a,a;
     -c,-c,-a,-c,-a,-a,-b;
     -c,-a,-c,-a,-a,-b,-c;
     -a,-c,-a,-a,-b,-c,-c;
      c,a,a,b,c,c,a;
      a,a,b,c,c,a,c]

private theorem X_mul_inverterShape (a b c : ZMod 11) : normalX * inverterShape a b c = product a b c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [normalX, Matrix.diagonal_mul, inverterShape, product]

private theorem square_eq (a b c : ZMod 11) : (normalX * inverterShape a b c)^2 = square a b c := by
  rw [X_mul_inverterShape, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, product, square] <;> ring

private theorem fifth_eq (a b c : ZMod 11) : ((normalX * inverterShape a b c)^5) 0 0 = fifthEntry a b c := by
  rw [show (5 : ℕ) = 2 + 2 + 1 from rfl, pow_add, pow_add, pow_one, square_eq, X_mul_inverterShape]
  simp [Matrix.mul_apply, Fin.sum_univ_succ, product, square, fifthEntry]
  ring

set_option synthInstance.maxSize 256 in
private theorem scalar_rigidity : ∀ a b c : ZMod 11,
    3*a^2 + b^2 + 3*c^2 = 1 →
    a^2 + a*b + 3*a*c + b*c + c^2 = 0 →
    fifthEntry a b c = 1 → a = 3 ∧ b = 9 ∧ c = 1 := by
  decide +kernel


private theorem inverter_parameters (a b c : ZMod 11)
    (h2 : inverterShape a b c ^ 2 = 1)
    (h5 : (normalX * inverterShape a b c) ^ 5 = 1) :
    a = 3 ∧ b = 9 ∧ c = 1 := by
  have h00 : 3*a^2 + b^2 + 3*c^2 = 1 := by
    calc
      _ = (inverterShape a b c ^ 2) 0 0 := by
        simp [pow_two, Matrix.mul_apply, Fin.sum_univ_succ, inverterShape]
        ring
      _ = 1 := by rw [h2]; rfl
  have h01 : a^2 + a*b + 3*a*c + b*c + c^2 = 0 := by
    calc
      _ = (inverterShape a b c ^ 2) 0 1 := by
        simp [pow_two, Matrix.mul_apply, Fin.sum_univ_succ, inverterShape]
        ring
      _ = 0 := by rw [h2]; rfl
  have h05 : fifthEntry a b c = 1 := by rw [← fifth_eq, h5]; rfl
  exact scalar_rigidity a b c h00 h01 h05

/-- The two normalizer relations and the source power relations force the
literal second matrix in (6.1), once x,y,u have the specified coordinates. -/
public theorem matrix_eq_sourceV (W : Matrix (Fin 7) (Fin 7) (ZMod 11))
    (hY : W * sourceY = sourceY.transpose * W)
    (hU : W * normalU = normalU * W)
    (h2 : W ^ 2 = 1) (h5 : (normalX * W) ^ 5 = 1) :
    normalX * W = sourceV := by
  rw [inverter_shape_of_relations W hY hU] at h2 h5 ⊢
  obtain ⟨ha, hb, hc⟩ := inverter_parameters (W 0 0) (W 0 1) (W 0 2) h2 h5
  rw [ha, hb, hc]
  decide +kernel

end CFSG.Quasithin.Janko1RelatorPair.SevenNormalization.MatrixCalculation
