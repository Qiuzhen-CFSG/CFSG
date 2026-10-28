module

public import Theory.SpecificGroups.BinaryLinear.Parabolics
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Binary matrix models and inverse transpose

The determinant of every invertible binary matrix is one, and the scalar
center of SLₙ(2) is trivial for positive n. Thus the actual central quotient
PSLₙ(2) is multiplicatively equivalent to the group of linear automorphisms
of its natural binary vector space. The comparison sends a matrix coset
to its usual action, rather than identifying models from their orders.

Inverse transpose is an involutive automorphism of SLₙ(2); transporting
through this comparison defines its action on the linear-map model.
These constructions do not assert coverage of arbitrary automorphisms.

Source: GLS3, Theorem 2.5.12(b–e,i) and §2.7, especially the matrix formulas
in `refs/KGroup/GLS3/chapter2.tex`, lines 1111–1115. The binary comparison
proofs follow the private constructions in `BinaryLinear.SylowCenters`;
the inverse-transpose calculation follows `PSL3.OuterSolvable.Actions`.
-/

@[expose] public section

open scoped MatrixGroups

namespace BinaryLinear.OuterCyclic

abbrev Space (n : ℕ) := Fin n → ZMod 2
abbrev LinearGroup (n : ℕ) := BinaryLinear.GL (Space n)

noncomputable def matrixEquivLinear (n : ℕ) :
    Matrix.GeneralLinearGroup (Fin n) (ZMod 2) ≃* LinearGroup n :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Space n))

theorem binary_toGL_surjective (n : ℕ) :
    Function.Surjective (Matrix.SpecialLinearGroup.toGL :
      SL(n, ZMod 2) →* Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) := by
  intro g
  have hu : ∀ u : (ZMod 2)ˣ, u = 1 := by decide
  have hd : Matrix.det (g : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 :=
    congrArg Units.val (hu (Matrix.GeneralLinearGroup.det g))
  exact ⟨⟨g, hd⟩, Units.ext rfl⟩

noncomputable def slEquivLinear (n : ℕ) : SL(n, ZMod 2) ≃* LinearGroup n :=
  (MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
    ⟨Matrix.SpecialLinearGroup.toGL_injective, binary_toGL_surjective n⟩).trans
      (matrixEquivLinear n)

theorem slEquivLinear_apply (n : ℕ) (x : SL(n, ZMod 2)) (v : Space n) :
    slEquivLinear n x v = (x : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec v := rfl

theorem binary_center_eq_bot {n : ℕ} (hn : 0 < n) :
    Subgroup.center SL(n, ZMod 2) = ⊥ := by
  apply eq_bot_iff.mpr
  intro g hg
  change g = 1
  obtain ⟨a, ha, hga⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  have ha0 : a ≠ 0 := by
    intro hzero
    simp [hzero, hn.ne'] at ha
  have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha0
  apply Subtype.ext
  simpa [ha1] using hga.symm

noncomputable def projectiveEquivSL {n : ℕ} (hn : 0 < n) :
    PSL(n, ZMod 2) ≃* SL(n, ZMod 2) :=
  (MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center SL(n, ZMod 2)))
    ⟨by rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', binary_center_eq_bot hn],
      QuotientGroup.mk'_surjective _⟩).symm

noncomputable def projectiveEquivLinear {n : ℕ} (hn : 0 < n) :
    PSL(n, ZMod 2) ≃* LinearGroup n :=
  (projectiveEquivSL hn).trans (slEquivLinear n)

theorem projectiveEquivLinear_mk {n : ℕ} (hn : 0 < n) (x : SL(n, ZMod 2)) :
    projectiveEquivLinear hn (QuotientGroup.mk x) = slEquivLinear n x :=
  congrArg (slEquivLinear n) ((projectiveEquivSL hn).apply_symm_apply x)

private theorem transpose_mul {n : ℕ} (x y : SL(n, ZMod 2)) :
    Matrix.SpecialLinearGroup.transpose (x * y) =
      Matrix.SpecialLinearGroup.transpose y * Matrix.SpecialLinearGroup.transpose x := by
  apply Subtype.ext
  exact Matrix.transpose_mul _ _

private theorem transpose_transpose {n : ℕ} (x : SL(n, ZMod 2)) :
    Matrix.SpecialLinearGroup.transpose (Matrix.SpecialLinearGroup.transpose x) = x := by
  apply Subtype.ext
  exact Matrix.transpose_transpose _

private theorem transpose_inv {n : ℕ} (x : SL(n, ZMod 2)) :
    Matrix.SpecialLinearGroup.transpose x⁻¹ = (Matrix.SpecialLinearGroup.transpose x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← transpose_mul, mul_inv_cancel]
  apply Subtype.ext
  exact Matrix.transpose_one

def graphSL (n : ℕ) : MulAut SL(n, ZMod 2) where
  toFun x := (Matrix.SpecialLinearGroup.transpose x)⁻¹
  invFun x := (Matrix.SpecialLinearGroup.transpose x)⁻¹
  left_inv x := by
    dsimp only
    rw [transpose_inv, transpose_transpose, inv_inv]
  right_inv x := by
    dsimp only
    rw [transpose_inv, transpose_transpose, inv_inv]
  map_mul' x y := by rw [transpose_mul, _root_.mul_inv_rev]

theorem graphSL_sq (n : ℕ) : graphSL n ^ 2 = 1 := by
  apply MulEquiv.ext
  intro x
  change (Matrix.SpecialLinearGroup.transpose (Matrix.SpecialLinearGroup.transpose x)⁻¹)⁻¹ = x
  rw [transpose_inv, transpose_transpose, inv_inv]

noncomputable def graphLinear (n : ℕ) : MulAut (LinearGroup n) :=
  MulAut.congr (slEquivLinear n) (graphSL n)

theorem graphLinear_slEquivLinear (n : ℕ) (x : SL(n, ZMod 2)) :
    graphLinear n (slEquivLinear n x) =
      slEquivLinear n (Matrix.SpecialLinearGroup.transpose x)⁻¹ := by
  change slEquivLinear n (graphSL n ((slEquivLinear n).symm (slEquivLinear n x))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem graphLinear_sq (n : ℕ) : graphLinear n ^ 2 = 1 := by
  rw [graphLinear, ← map_pow, graphSL_sq, map_one]

end BinaryLinear.OuterCyclic
