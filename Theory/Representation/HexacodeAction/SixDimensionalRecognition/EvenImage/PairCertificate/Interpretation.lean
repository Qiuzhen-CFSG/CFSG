module
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.EvenImage.Operators
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.EvenImage.PairCertificate.Data
public import Mathlib.LinearAlgebra.Matrix.ToLin
/-!
# Interpreting the pair certificate on the literal hexacode

The finite four-symbol arithmetic is identified with the existing quadratic
field, entry by entry. The matrix homomorphism uses `fieldCoordinates` on the
actual hexacode carrier, and the coordinate theorems in `Operators` identify
both model generators. Inverse matrix pairs construct actual linear
automorphisms of that same carrier.

This is the interpretation boundary for the finite K.1.3 certificate,
Aschbacher–Smith, printed p.453 (PDF p.464).
-/

@[expose] public section
open Atlas.Codes
namespace Representation.Hexacode.SixDimensional.EvenImage.PairData
open Q
abbrev Mat := Matrix (Fin 3) (Fin 3) F

def value : Q → F
  | z => 0
  | o => 1
  | w => omega
  | t => omega ^ 2

def symbol (x : F) : Q :=
  if x.im = 0 then (if x.re = 0 then z else o)
  else (if x.re = 0 then w else t)

theorem value_symbol : ∀ x : F, value (symbol x) = x := by decide +kernel
theorem symbol_value : ∀ x : Q, symbol (value x) = x := by decide +kernel
theorem value_add : ∀ x y : Q, value (add x y) = value x + value y := by decide +kernel
theorem value_mul : ∀ x y : Q, value (mul x y) = value x * value y := by decide +kernel

def decode (m : M) : Mat :=
  !![value m.a,value m.b,value m.c;
     value m.d,value m.e,value m.f;
     value m.g,value m.h,value m.i]
def encode (m : Mat) : M :=
  ⟨symbol (m 0 0),symbol (m 0 1),symbol (m 0 2),
   symbol (m 1 0),symbol (m 1 1),symbol (m 1 2),
   symbol (m 2 0),symbol (m 2 1),symbol (m 2 2)⟩
theorem decode_encode (m : Mat) : decode (encode m) = m := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> exact value_symbol _
theorem encode_decode (m : M) : encode (decode m) = m := by
  cases m
  simp only [encode, decode, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, symbol_value]
theorem decode_injective : Function.Injective decode := Function.LeftInverse.injective encode_decode

theorem decode_ident : decode ident = 1 := by decide +kernel

theorem decode_mm (a b : M) : decode (mm a b) = decode a * decode b := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [decode, mm, Matrix.mul_apply, Fin.sum_univ_succ, value_add, value_mul, add_assoc]

noncomputable def matrixRing : Module.End F hexacode ≃+* Mat :=
  fieldCoordinates.conjRingEquiv.trans LinearMap.toMatrixAlgEquiv'.toRingEquiv
noncomputable def matrix : FieldGL →* Mat :=
  matrixRing.toMonoidHom.comp LinearEquiv.automorphismGroup.toLinearMapMonoidHom

theorem matrix_injective : Function.Injective matrix := by
  intro v u h
  have h' := matrixRing.injective h
  exact LinearEquiv.toLinearMap_injective h'

theorem matrix_apply (v : FieldGL) (x : Fin 3 → F) :
    (matrix v).mulVec x = fieldCoordinates (v (fieldCoordinates.symm x)) := by
  change (LinearMap.toMatrix' (fieldCoordinates.conjRingEquiv v.toLinearMap)).mulVec x = _
  rw [LinearMap.toMatrix'_mulVec]
  rfl

theorem matrix_first : matrix fieldGenerator = decode first := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change (matrix fieldGenerator).mulVec x = (decode first).mulVec x
  rw [matrix_apply]
  change fieldCoordinates (evenFieldAction generatorA (fieldCoordinates.symm x)) = _
  rw [generatorA_coordinates, fieldCoordinates.apply_symm_apply]
  funext i
  fin_cases i <;> simp [decode, first, value, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_assoc]

theorem matrix_second : matrix (evenFieldAction generatorB) = decode second := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change (matrix (evenFieldAction generatorB)).mulVec x = (decode second).mulVec x
  rw [matrix_apply, generatorB_coordinates, fieldCoordinates.apply_symm_apply]
  funext i
  fin_cases i <;> simp [decode, second, value, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

noncomputable def ofMatrices (m n : Mat) (hmn : m*n=1) (hnm : n*m=1) : FieldGL :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv F hexacode)
    ((Units.mapEquiv matrixRing.symm.toMulEquiv) ⟨m,n,hmn,hnm⟩)

theorem matrix_ofMatrices (m n : Mat) (hmn : m*n=1) (hnm : n*m=1) :
    matrix (ofMatrices m n hmn hnm) = m := by
  change matrixRing (matrixRing.symm m) = m
  exact matrixRing.apply_symm_apply m
end Representation.Hexacode.SixDimensional.EvenImage.PairData
