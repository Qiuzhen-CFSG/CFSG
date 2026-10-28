module
public import Theory.Representation.OrthogonalFourPlusMatrix.Binary
public import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Tactic.Ring

/-!
# The natural tensor model for the split orthogonal four-space

The alternating form identifies the second natural SL₂ module with its dual.
Tensor coordinates then send `u ⊗ v` to the rank-one matrix with column u
and row (-v₁,v₀). The actual two-factor tensor action becomes exactly
`M ↦ A M B⁻¹`. Both the linear equivalence and equivariance are proved,
so the binary restriction can be used by the exclusion consumer.

Source: Aschbacher–Smith, G.11.2(7), printed p.364 (PDF p.375), and the
proof of 6.2.19, printed p.691 (PDF p.708).
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace Representation.RankTwo.OrthogonalFour
open ClassicalOrthogonal.FourPlusMatrix
open Matrix

variable {K : Type*} [Field K]

/-- The alternating pairing identifies the natural SL₂ module with its dual. -/
def naturalDual : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) where
  toFun v := ![-v 1, v 0]
  invFun v := ![v 1, -v 0]
  left_inv v := by funext i; fin_cases i <;> simp
  right_inv v := by funext i; fin_cases i <;> simp
  map_add' v w := by funext i; fin_cases i <;> simp [add_comm]
  map_smul' c v := by funext i; fin_cases i <;> simp

/-- Actual tensor coordinates, with the second natural module identified with
the dual by the invariant alternating form. -/
def tensorCoordinates :
    ((Fin 2 → K) ⊗[K] (Fin 2 → K)) ≃ₗ[K] Mat (F := K) :=
  (TensorProduct.congr (LinearEquiv.refl K (Fin 2 → K)) naturalDual).trans
    ((TensorProduct.piScalarRight K K (Fin 2 → K) (Fin 2)).trans
      (Matrix.transposeLinearEquiv (Fin 2) (Fin 2) K K))

theorem tensorCoordinates_tmul (u v : Fin 2 → K) :
    tensorCoordinates (u ⊗ₜ[K] v) = Matrix.vecMulVec u (naturalDual v) := by
  apply Matrix.ext
  intro i j
  change (TensorProduct.piScalarRight K K (Fin 2 → K) (Fin 2)
    (TensorProduct.congr (LinearEquiv.refl K (Fin 2 → K)) naturalDual
      (u ⊗ₜ[K] v))) j i = u i * naturalDual v j
  rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  exact mul_comm _ _

private theorem naturalDual_action (B : Matrix.SpecialLinearGroup (Fin 2) K)
    (v : Fin 2 → K) : naturalDual (B.val *ᵥ v) = (naturalDual v) ᵥ* B⁻¹.val := by
  funext i
  fin_cases i <;>
    simp [naturalDual, Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two] <;> ring

/-- The two natural SL₂ actions, tensored over the coefficient field. -/
def tensorRepresentation : Representation K (PairSL (F := K))
    ((Fin 2 → K) ⊗[K] (Fin 2 → K)) :=
  Representation.tprod
    ((Representation.specialLinearNatural 2).comp (MonoidHom.fst _ _))
    ((Representation.specialLinearNatural 2).comp (MonoidHom.snd _ _))

/-- The tensor and determinant models intertwine element by element. -/
theorem tensorCoordinates_equivariant (g : PairSL (F := K))
    (z : (Fin 2 → K) ⊗[K] (Fin 2 → K)) :
    tensorCoordinates (tensorRepresentation g z) = representation g (tensorCoordinates z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    change tensorCoordinates ((g.1.val *ᵥ u) ⊗ₜ[K] (g.2.val *ᵥ v)) =
      g.1.val * tensorCoordinates (u ⊗ₜ[K] v) * g.2⁻¹.val
    rw [tensorCoordinates_tmul, tensorCoordinates_tmul, naturalDual_action,
      Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  | add z w hz hw => simp only [map_add, hz, hw]

end Representation.RankTwo.OrthogonalFour
