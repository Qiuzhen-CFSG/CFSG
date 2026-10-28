module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical.Structure

/-!
# Cubic fixed vectors at the unitary-four short root

The binary cubic matrix acts on the Hermitian plane radical by congruence.
Its fixed matrices are exactly [[b+σ(b),b],[σ(b),b+σ(b)]]. The binary
reflection fixes such a matrix precisely when σ(b)=b. Thus the cubic
fixed space and the fixed space of the full S₃ are distinct.

A trace-one, norm-one parameter gives a long-root matrix in the cubic
fixed space. An explicit lower Levi shear conjugates the marked long
root to this matrix. These literal coordinates supply the adequate
fixed-space argument in Aschbacher–Smith F.4.42, printed pp.295–296.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
open Representation.OrthogonalFourMinus
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourPlaneLocal
variable (F : Type*) [Field F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)

/-- The cubic in the binary Levi subgroup. -/
def cubic : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0,1;1,1], by simp [det_fin_two, CharTwo.neg_eq]⟩

/-- The reflection completing the cubic to the binary S₃. -/
def reflection : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0,1;1,0], by simp [det_fin_two, CharTwo.neg_eq]⟩

/-- The marked short-root Hermitian matrix. -/
def shortParameter : hermitianMatrices F σ :=
  ⟨!![0,1;1,0], by ext i j; fin_cases i <;> fin_cases j <;> simp [adjoint]⟩

/-- The marked long-root Hermitian matrix. -/
def longParameter : hermitianMatrices F σ :=
  ⟨!![1,0;0,0], by ext i j; fin_cases i <;> fin_cases j <;> simp [adjoint]⟩

/-- One field parameter describes every cubic-fixed Hermitian matrix. -/
def fixedParameter (b : F) : hermitianMatrices F σ :=
  ⟨!![b + σ b,b;σ b,b + σ b], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adjoint, hσ b, add_comm]⟩

theorem cubic_cube : cubic F ^ 3 = 1 := by
  apply Subtype.ext
  change ( !![0,1;1,1] : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1
  rw [pow_succ, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,
      Fin.sum_univ_two, CharTwo.add_self_eq_zero]

theorem cubic_ne_one : cubic F ≠ 1 := by
  intro he
  have h := congrArg (fun A : SpecialLinearGroup (Fin 2) F => A.val 0 0) he
  exact zero_ne_one h

theorem cubic_order : orderOf (cubic F) = 3 :=
  orderOf_eq_prime_iff.mpr ⟨cubic_cube F, cubic_ne_one F⟩

theorem fixedParameter_fixed (b : F) :
    hermitianCongruence F σ hσ (cubic F) (fixedParameter F σ hσ b) =
      fixedParameter F σ hσ b := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianCongruence, cubic, fixedParameter, adjoint, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, add_comm, add_left_comm, CharTwo.add_self_eq_zero,
      CharTwo.add_cancel_left]

/-- This exhausts the cubic fixed space, not just selected fixed vectors. -/
theorem cubic_fixed_iff (X : hermitianMatrices F σ) :
    hermitianCongruence F σ hσ (cubic F) X = X ↔
      X = fixedParameter F σ hσ (X.val 0 1) := by
  constructor
  · intro he
    have h00 := congrArg (fun Y : hermitianMatrices F σ => Y.val 0 0) he
    have h01 := congrArg (fun Y : hermitianMatrices F σ => Y.val 0 1) he
    simp [hermitianCongruence, cubic, adjoint, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h00 h01
    have hx : σ (X.val 0 1) = X.val 1 0 := congrFun (congrFun X.property 1) 0
    have hd : X.val 0 0 = X.val 0 1 + σ (X.val 0 1) := by
      rw [hx, ← h01, h00]
      simp [add_comm, add_left_comm, CharTwo.add_self_eq_zero]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact hd
    · rfl
    · exact hx.symm
    · exact h00.trans hd
  · intro he
    rw [he]
    exact fixedParameter_fixed F σ hσ _

/-- The cubic fixed-space count is the order of the quadratic field. -/
def cubicFixedEquiv :
    {X : hermitianMatrices F σ // hermitianCongruence F σ hσ (cubic F) X = X} ≃ F where
  toFun X := X.val.val 0 1
  invFun b := ⟨fixedParameter F σ hσ b, fixedParameter_fixed F σ hσ b⟩
  left_inv X := Subtype.ext ((cubic_fixed_iff F σ hσ X.val).mp X.property).symm
  right_inv _ := rfl

theorem cubic_fixed_card :
    Nat.card {X : hermitianMatrices F σ //
      hermitianCongruence F σ hσ (cubic F) X = X} = Nat.card F :=
  Nat.card_congr (cubicFixedEquiv F σ hσ)

/-- The reflection fixes the cubic parameter exactly over the fixed field. -/
theorem reflection_fixedParameter_iff (b : F) :
    hermitianCongruence F σ hσ (reflection F) (fixedParameter F σ hσ b) =
      fixedParameter F σ hσ b ↔ σ b = b := by
  constructor
  · intro he
    have h := congrArg (fun Y : hermitianMatrices F σ => Y.val 0 1) he
    simpa [hermitianCongruence, reflection, fixedParameter, adjoint, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two] using h
  · intro hb
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hermitianCongruence, reflection, fixedParameter, adjoint, Matrix.vecMul, dotProduct,
        Fin.sum_univ_two, hb]

/-- The trace-zero parameter one is precisely the marked short root. -/
theorem fixedParameter_one : fixedParameter F σ hσ 1 = shortParameter F σ := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fixedParameter, shortParameter, CharTwo.add_self_eq_zero]

/-- The explicit lower Levi shear taking the long root to the norm-one parameter. -/
def longConjugator (b : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1,0;σ b,1], by simp [det_fin_two]⟩

omit [CharP F 2] in
theorem long_congruence (b : F) (ht : b + σ b = 1) (hn : b * σ b = 1) :
    hermitianCongruence F σ hσ (longConjugator F σ b) (longParameter F σ) =
      fixedParameter F σ hσ b := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianCongruence, longConjugator, longParameter, fixedParameter, adjoint,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two, hσ b, ht, hn, mul_comm]

variable [Finite F]

/-- In the actual SU₄ matrices this cubic-fixed vector is conjugate to
the marked long root by an element of the plane Levi. -/
theorem long_unipotent_conjugation (b : F) (ht : b + σ b = 1) (hn : b * σ b = 1) :
    (levi F σ hσ (longConjugator F σ b)).val * unipotentSU F σ hσ (longParameter F σ) *
      (levi F σ hσ (longConjugator F σ b)).val⁻¹ =
        unipotentSU F σ hσ (fixedParameter F σ hσ b) := by
  rw [unipotentSU_conj, factorRestriction_levi, long_congruence F σ hσ b ht hn]

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot
