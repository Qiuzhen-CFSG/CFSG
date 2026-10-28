module

public import Theory.Representation.SL3.AdjointCubicCentralizer

/-!
# The determinant twist changes the cubic fixed space

Conjugation on trace-zero three-by-three matrices can be tensored with the
determinant character. The twisted action agrees with conjugation on every
special linear element, but diag(ω,1,1) fixes only the lower-left column when
ω and ω² are both nonidentity. Its fixed space therefore has dimension two,
where the untwisted fixed space has dimension four.

This identifies an extension issue in the proof of Aschbacher–Smith B.4.14,
printed p.98: identification of an SL₃ constituent alone does not identify
the PGL₃ action. The calculations here do not assert binary irreducibility
or verify all chief-factor hypotheses of that lemma.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix
namespace Representation.SL3.AdjointCubicCentralizer
variable (K : Type*) [Field K]

/-- Tensoring conjugation with the determinant character. -/
def determinantTwist : Representation K (Mat3 K)ˣ (Mat3 K) where
  toFun g := Matrix.det g.val • conjugation K 3 g
  map_one' := by ext X i j; simp [conjugation]
  map_mul' g h := by
    ext X i j
    change (Matrix.det (g*h).val • (conjugation K 3 (g*h) X)) i j =
      (Matrix.det g.val • conjugation K 3 g
        (Matrix.det h.val • conjugation K 3 h X)) i j
    rw [map_mul, Module.End.mul_apply, map_smul, smul_smul]
    simp only [Units.val_mul, Matrix.det_mul]

/-- A determinant twist is invisible on the whole special linear group. -/
theorem determinantTwist_specialLinear (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    determinantTwist K (Matrix.SpecialLinearGroup.toGL g) =
      conjugation K 3 (Matrix.SpecialLinearGroup.toGL g) := by
  change Matrix.det g.val • conjugation K 3 (Matrix.SpecialLinearGroup.toGL g) = _
  rw [g.property, one_smul]

private theorem det_block (a : K) (D : Mat2 K) :
    Matrix.det (block K a D) = a * Matrix.det D := by
  simp [block, Matrix.det_fin_three, Matrix.det_fin_two, mul_sub, mul_assoc]

/-- The two-dimensional column space fixed by the determinant-twisted cubic. -/
def column : (Fin 2 → K) →ₗ[K] Mat3 K where
  toFun v := !![0,0,0; v 0,0,0; v 1,0,0]
  map_add' v w := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_smul' c v := by ext i j; fin_cases i <;> fin_cases j <;> simp

/-- The literal trace-zero fixed space for the twisted representation. -/
def twistedFixedSpace (ω : Kˣ) : Submodule K (Mat3 K) where
  carrier := {X | Matrix.trace X = 0 ∧ determinantTwist K (diagonalUnit K ω) X = X}
  zero_mem' := by simp
  add_mem' := by
    rintro X Y ⟨hX,hX'⟩ ⟨hY,hY'⟩
    exact ⟨by simp [hX,hY], by simp [hX',hY']⟩
  smul_mem' := by
    rintro c X ⟨hX,hX'⟩
    exact ⟨by simp [hX], by simp [hX']⟩

private theorem twisted_apply (ω : Kˣ) (X : Mat3 K) :
    determinantTwist K (diagonalUnit K ω) X =
      !![(ω : K) * X 0 0, (ω : K)^2 * X 0 1, (ω : K)^2 * X 0 2;
         X 1 0, (ω : K) * X 1 1, (ω : K) * X 1 2;
         X 2 0, (ω : K) * X 2 1, (ω : K) * X 2 2] := by
  change (Matrix.det (block K (ω : K) 1)) •
    (block K (ω : K) 1 * X * block K (↑ω⁻¹ : K) 1) = _
  rw [det_block, Matrix.det_one, mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_three] <;>
    simp [block, pow_two, mul_assoc, mul_left_comm, mul_comm]

theorem column_mem_twistedFixedSpace (ω : Kˣ) (v : Fin 2 → K) :
    column K v ∈ twistedFixedSpace K ω := by
  constructor
  · simp [column, Matrix.trace, Fin.sum_univ_three]
  · rw [twisted_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [column]

private theorem twisted_eq_column (ω : Kˣ) (hω : (ω : K) ≠ 1)
    (hω2 : (ω : K)^2 ≠ 1) (X : twistedFixedSpace K ω) :
    column K ![X.val 1 0, X.val 2 0] = X.val := by
  have hfix := X.property.2
  rw [twisted_apply] at hfix
  have h (i j : Fin 3) := congrArg (fun M : Mat3 K => M i j) hfix
  have kill (a z : K) (ha : a ≠ 1) (hz : a*z = z) : z = 0 := by
    have hz' : (a-1)*z = 0 := by rw [sub_mul, one_mul, hz, sub_self]
    exact (mul_eq_zero.mp hz').resolve_left (sub_ne_zero.mpr ha)
  have h00 := kill _ _ hω (h 0 0)
  have h01 := kill _ _ hω2 (h 0 1)
  have h02 := kill _ _ hω2 (h 0 2)
  have h11 := kill _ _ hω (h 1 1)
  have h12 := kill _ _ hω (h 1 2)
  have h21 := kill _ _ hω (h 2 1)
  have h22 := kill _ _ hω (h 2 2)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [column, h00,h01,h02,h11,h12,h21,h22]

/-- The actual twisted fixed space is a two-space. -/
def twistedFixedEquiv (ω : Kˣ) (hω : (ω : K) ≠ 1) (hω2 : (ω : K)^2 ≠ 1) :
    twistedFixedSpace K ω ≃ₗ[K] (Fin 2 → K) where
  toFun X := ![X.val 1 0, X.val 2 0]
  invFun v := ⟨column K v, column_mem_twistedFixedSpace K ω v⟩
  left_inv X := by exact Subtype.ext (twisted_eq_column K ω hω hω2 X)
  right_inv v := by ext i; fin_cases i <;> rfl
  map_add' X Y := by ext i; fin_cases i <;> rfl
  map_smul' c X := by ext i; fin_cases i <;> rfl

theorem finrank_twistedFixedSpace (ω : Kˣ) (hω : (ω : K) ≠ 1) (hω2 : (ω : K)^2 ≠ 1) :
    Module.finrank K (twistedFixedSpace K ω) = 2 := by
  rw [(twistedFixedEquiv K ω hω hω2).finrank_eq]
  exact Module.finrank_fin_fun K

/-- A nonidentity cubic scalar has nonidentity square. -/
theorem square_ne_one_of_cube (ω : Kˣ) (hω : (ω : K) ≠ 1) (hcube : (ω : K)^3 = 1) :
    (ω : K)^2 ≠ 1 := by
  intro h
  apply hω
  simpa only [pow_succ, h, one_mul] using hcube

end Representation.SL3.AdjointCubicCentralizer
