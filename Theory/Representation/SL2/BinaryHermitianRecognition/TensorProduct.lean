module

public import Theory.Representation.SL2.BinaryHermitianRecognition.ScalarExtension
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# The Hermitian scalar extension as an actual tensor product

The coordinate map sends x ⊗ y to the outer-product matrix xyᵀ. It
intertwines the tensor of the natural action and its s-th Frobenius twist
with the matrix pair action already used for Hermitian recognition.
Composing with the proved Hermitian scalar-extension map yields the literal
N ⊗ N^σ equivalence over GF(2^(2s)), for every positive s, including s=1.
The coefficient field is the actual Frobenius fixed subfield; its extension
degree two is `OrthogonalFourMinus.FiniteModel.finrank_field`.

Source: GLS volume 3, §§2.8.6, 2.8.8, 2.8.10(b); Aschbacher–Smith,
combined manuscript (1 March 2004), K.3.1, printed pp.453–454.
-/

@[expose] public section
open scoped MatrixGroups TensorProduct
open Representation Representation.SL2

namespace Representation.SL2.BinaryHermitian
noncomputable section
open Representation.OrthogonalFourMinus Representation.OrthogonalFourMinus.FiniteModel
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Tensor coordinates preserve the order of the two natural factors. -/
def tensorCoordinates : ((Fin 2 → F) ⊗[F] (Fin 2 → F)) ≃ₗ[F] Mat F :=
  (_root_.TensorProduct.comm F (Fin 2 → F) (Fin 2 → F)).trans
    (_root_.TensorProduct.piScalarRight F F (Fin 2 → F) (Fin 2))

omit [Finite F] [CharP F 2] in
@[simp] theorem tensorCoordinates_tmul (x y : Fin 2 → F) :
    tensorCoordinates (x ⊗ₜ[F] y) = Matrix.vecMulVec x y := by
  ext i j
  change (_root_.TensorProduct.piScalarRight F F (Fin 2 → F) (Fin 2))
    (y ⊗ₜ[F] x) i j = _
  rw [_root_.TensorProduct.piScalarRight_apply, _root_.TensorProduct.piScalarRightHom_tmul]
  rfl

/-- The matrix pair in Hermitian recognition is the literal tensor product
of the natural module and its s-th Frobenius twist. -/
def pairTensorEquiv (s : ℕ) :
    ((specialLinearNatural (k := F) 2).tprod (BinarySmall.frobeniusNatural s)).Equiv
      (BinaryHermitian.pair (RingHom.id F) s 0) := by
  refine Representation.Equiv.mk tensorCoordinates ?_
  intro g
  apply LinearMap.ext
  intro u
  induction u using _root_.TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simpa only [map_add] using congrArg₂ (· + ·) hu hv
  | tmul x y =>
    change tensorCoordinates
      (specialLinearNatural 2 g x ⊗ₜ[F] BinarySmall.frobeniusNatural s g y) =
        BinaryHermitian.pair (RingHom.id F) s 0 g (tensorCoordinates (x ⊗ₜ[F] y))
    rw [tensorCoordinates_tmul, tensorCoordinates_tmul, BinaryHermitian.pair_apply]
    simp only [RingHom.id_apply, pow_zero, pow_one, zero_add]
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    congr 1
    exact (Matrix.vecMul_transpose (g.val.map (iterateFrobeniusEquiv F 2 s)) y).symm

/-- Extend the four-dimensional fixed-field Hermitian action to its quadratic
field: this is the actual N tensor N^sigma identification, including s=1. -/
def hermitianScalarExtensionEquiv (s : ℕ) [NeZero s] :
    letI := BinaryHermitian.coefficientModule (RingEquiv.refl (fixedField s))
    (extendScalars (Field s)
      (BinaryHermitian.model (RingEquiv.refl (fixedField s)) (RingEquiv.refl (Field s)))).Equiv
        ((specialLinearNatural (k := Field s) 2).tprod (BinarySmall.frobeniusNatural s)) := by
  letI := BinaryHermitian.coefficientModule (RingEquiv.refl (fixedField s))
  exact (BinaryHermitian.scalarExtensionEquiv (RingEquiv.refl (fixedField s))
    (RingHom.id (Field s)) (fun _ => rfl) (RingHom.id (Field s))
    (RingEquiv.refl (Field s)) 0 (by intro x; simp)).trans (pairTensorEquiv s).symm
end
end Representation.SL2.BinaryHermitian
