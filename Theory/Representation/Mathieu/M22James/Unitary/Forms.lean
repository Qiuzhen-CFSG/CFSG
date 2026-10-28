module
public import Theory.Representation.Mathieu.M22James.Unitary.Action
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Invariant Hermitian and binary quadratic forms on the genuine module

Pull back the identity Hermitian form through the explicit field coordinates.
This gives a bundled form linear in its first argument and Frobenius-semilinear
in its second, for exactly the central-field module structure. The coordinate
equivalence proves nondegeneracy; the full matrix-action theorem proves
invariance. Taking the real part of the binary bilinear diagonal gives an
actual `QuadraticForm`. Hermitian symmetry puts that diagonal in F₂, proving
`algebraMap (q v) = f v v`, and hence invariance of q.

This establishes the native-module form assertions in Aschbacher–Smith
H.12.1(2), printed pp.393–394. Transport to arbitrary triple covers belongs
to the chapter's recognition assembly. See `Data` for ATLAS attribution.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.Unitary
open Matrix Representation.SL2FourNatural
open Uniqueness.PointRestriction (fieldModule)
open scoped Matrix

local instance : Module F BinarySpace :=
  fieldModule binaryRepresentation binaryRepresentation_faithful

def conjugateCoordinates : Vector →ₗ[ZMod 2] Vector where
  toFun v i := fieldFrobenius (v i)
  map_add' v w := by funext i; exact map_add _ _ _
  map_smul' c v := by
    funext i
    change fieldFrobenius (c • v i) = c • fieldFrobenius (v i)
    fin_cases c
    · change fieldFrobenius ((0 : ZMod 2) • v i) = (0 : ZMod 2) • _
      simp
    · change fieldFrobenius ((1 : ZMod 2) • v i) = (1 : ZMod 2) • _
      simp

def hermitianBinary : BinarySpace →ₗ[ZMod 2] BinarySpace →ₗ[ZMod 2] F :=
  (dotProductBilin (ZMod 2) (ZMod 2)).compl₁₂ binaryCoordinates.toLinearMap
    (conjugateCoordinates.comp binaryCoordinates.toLinearMap)

theorem hermitianBinary_apply (v w : BinarySpace) :
    hermitianBinary v w = coordinates v ⬝ᵥ (fun i => fieldFrobenius (coordinates w i)) := rfl

theorem hermitianBinary_smul_left (a : F) (v w : BinarySpace) :
    hermitianBinary (a • v) w = a * hermitianBinary v w := by
  simp only [hermitianBinary_apply, map_smul, smul_dotProduct, smul_eq_mul]

theorem hermitianBinary_smul_right (a : F) (v w : BinarySpace) :
    hermitianBinary v (a • w) = fieldFrobenius a * hermitianBinary v w := by
  simp only [hermitianBinary_apply, map_smul, Pi.smul_apply, smul_eq_mul, map_mul]
  simp only [dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Linear in the first argument and Frobenius-semilinear in the second. -/
def hermitianForm : BinarySpace →ₗ[F] BinarySpace →ₛₗ[fieldFrobenius.toRingHom] F where
  toFun v := {
    toFun := hermitianBinary v
    map_add' := (hermitianBinary v).map_add
    map_smul' a w := hermitianBinary_smul_right a v w }
  map_add' v w := by
    apply LinearMap.ext
    intro u
    exact LinearMap.congr_fun (hermitianBinary.map_add v w) u
  map_smul' a v := by
    apply LinearMap.ext
    intro w
    exact hermitianBinary_smul_left a v w

theorem hermitianForm_apply (v w : BinarySpace) :
    hermitianForm v w = coordinates v ⬝ᵥ (fun i => fieldFrobenius (coordinates w i)) := rfl

theorem hermitianForm_symmetry (v w : BinarySpace) :
    fieldFrobenius (hermitianForm v w) = hermitianForm w v := by
  simp only [hermitianForm_apply, dotProduct, map_sum, map_mul, fieldFrobenius_involutive]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem hermitianForm_separatingLeft : hermitianForm.SeparatingLeft := by
  intro v hv
  apply coordinates.injective
  rw [map_zero]
  funext i
  have h := hv (coordinates.symm (Pi.single i 1))
  have hs : (fun j => fieldFrobenius ((Pi.single i 1 : Vector) j)) = (Pi.single i 1 : Vector) := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  rw [hermitianForm_apply, coordinates.apply_symm_apply, hs, dotProduct_single_one] at h
  exact h

theorem hermitianForm_nondegenerate : hermitianForm.Nondegenerate := by
  refine ⟨hermitianForm_separatingLeft, ?_⟩
  intro v hv
  apply hermitianForm_separatingLeft v
  intro w
  rw [← hermitianForm_symmetry, hv, map_zero]

private theorem conjugate_mulVec (A : Matrix (Fin 6) (Fin 6) F) (v : Vector) :
    (fun i => fieldFrobenius ((A *ᵥ v) i)) =
      (fun i => fieldFrobenius (v i)) ᵥ* A.transpose.map fieldFrobenius := by
  funext i
  simp only [mulVec, vecMul, dotProduct, map_sum, map_mul, map_apply, transpose_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem hermitianForm_invariant (g : M22TripleCover) (v w : BinarySpace) :
    hermitianForm (binaryRepresentation g v) (binaryRepresentation g w) =
      hermitianForm v w := by
  simp only [hermitianForm_apply, ← matrixAction_intertwines]
  rw [dotProduct_comm, conjugate_mulVec, dotProduct_mulVec, vecMul_vecMul,
    matrixAction_unitary, vecMul_one, dotProduct_comm]

/-- The binary quadratic form is the real part of the Hermitian diagonal. -/
def quadraticForm : QuadraticForm (ZMod 2) BinarySpace :=
  (QuadraticAlgebra.reₗ 1 1).compQuadraticMap (LinearMap.BilinMap.toQuadraticMap hermitianBinary)

theorem quadraticForm_apply (v : BinarySpace) :
    quadraticForm v = (hermitianForm v v).re := rfl

theorem quadraticForm_diagonal (v : BinarySpace) :
    algebraMap (ZMod 2) F (quadraticForm v) = hermitianForm v v := by
  have hfix : fieldFrobenius (hermitianForm v v) = hermitianForm v v :=
    hermitianForm_symmetry v v
  rcases (fieldFrobenius_fixed _).mp hfix with h | h
  · rw [quadraticForm_apply, h]
    rfl
  · rw [quadraticForm_apply, h]
    rfl

theorem quadraticForm_invariant (g : M22TripleCover) (v : BinarySpace) :
    quadraticForm (binaryRepresentation g v) = quadraticForm v := by
  simp only [quadraticForm_apply, hermitianForm_invariant]

end Sporadic.Mathieu.M22TripleCover.Unitary
