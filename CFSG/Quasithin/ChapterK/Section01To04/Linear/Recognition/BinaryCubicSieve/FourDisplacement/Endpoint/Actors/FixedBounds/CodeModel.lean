module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Actors.FixedBounds.Coordinates

/-!
# Concrete codes for upper unitriangular and reversing graph actors

A code has six upper-triangular bits and one graph bit. The matrix action is
proved equivalent to the literal normalizer action on the adjoint quotient.
Every coded actor belongs to `standardActors`; exhaustive coverage is not
asserted in this module.

Source: Guralnick–Malle, Classification of 2F-modules II, Lemma 4.5 and
Proposition 4.8 step 3A; Aschbacher–Smith K.3.2, printed pp.454–455.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public section
open Representation Representation.BinaryOffender Matrix
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.FixedBounds
abbrev Code := Fin 128

def codeBits (c : Code) : Fin 6 → ZMod 2 := fun j => (c.val / 2 ^ (j.val + 1) : ℕ)

def codeOuter (c : Code) : Bool := c.val % 2 == 1

def upperMatrix (b : Fin 6 → ZMod 2) : ActorMatrix :=
  !![1, b 0, b 1, b 2; 0, 1, b 3, b 4; 0, 0, 1, b 5; 0, 0, 0, 1]

def upperInverse (b : Fin 6 → ZMod 2) : ActorMatrix :=
  !![1, b 0, b 1 + b 0 * b 3, b 2 + b 0 * b 4 + b 1 * b 5 + b 0 * b 3 * b 5;
    0, 1, b 3, b 4 + b 3 * b 5; 0, 0, 1, b 5; 0, 0, 0, 1]

theorem upperMatrix_det (b : Fin 6 → ZMod 2) : (upperMatrix b).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (by
    intro i j hji
    fin_cases i <;> fin_cases j <;> simp_all [upperMatrix])]
  simp [upperMatrix, Fin.prod_univ_succ]

theorem upperMatrix_mul_upperInverse (b : Fin 6 → ZMod 2) :
    upperMatrix b * upperInverse b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperMatrix, upperInverse, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp [CharTwo.two_eq_zero]

def upperElement (b : Fin 6 → ZMod 2) : Group := ⟨upperMatrix b, upperMatrix_det b⟩

theorem upperElement_upper (b : Fin 6 → ZMod 2) : IsUpperUnitriangular (upperElement b) := by
  constructor
  · intro i; fin_cases i <;> rfl
  · intro i j hji; fin_cases i <;> fin_cases j <;> simp_all [upperElement, upperMatrix]

theorem upperElement_inv (b : Fin 6 → ZMod 2) :
    (upperElement b)⁻¹.val = upperInverse b := by
  calc
    _ = (upperElement b)⁻¹.val * (upperMatrix b * upperInverse b) := by
      rw [upperMatrix_mul_upperInverse, Matrix.mul_one]
    _ = ((upperElement b)⁻¹.val * (upperElement b).val) * upperInverse b :=
      (Matrix.mul_assoc _ _ _).symm
    _ = upperInverse b := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
      exact Matrix.one_mul _

noncomputable def codeActor (c : Code) : linearNormalizer adjoint :=
  innerActor (upperElement (codeBits c)) * if codeOuter c then reversingGraphActor else 1

theorem codeActor_mem_standardActors (c : Code) : codeActor c ∈ standardActors := by
  apply standardActors.mul_mem
  · exact innerActor_mem_standardActors _ (upperElement_upper _)
  · split_ifs
    · exact reversingGraphActor_mem_standardActors
    · exact standardActors.one_mem

def actMatrix (c : Code) : Matrix (Fin 14) (Fin 14) (ZMod 2) := fun i j =>
  pack (upperMatrix (codeBits c) *
    (if codeOuter c then reverseMatrix * (unpack (Pi.single j 1)).transpose * reverseMatrix
    else unpack (Pi.single j 1)) * upperInverse (codeBits c)) i

noncomputable def coordinateAction (c : Code) : Module.End (ZMod 2) Coordinates :=
  coordinateEquiv.toLinearMap.comp
    ((normalizerRepresentation adjoint (codeActor c)).comp coordinateEquiv.symm.toLinearMap)

theorem matrix_traceAction (g : Group) (f : TraceZero) :
    LinearMap.toMatrix' (traceAction g f).val =
      g.val * LinearMap.toMatrix' f.val * g⁻¹.val := by
  simp only [traceAction_apply, LinearMap.toMatrix'_comp, natural_matrix]
  exact (Matrix.mul_assoc _ _ _).symm

@[simp] theorem unpackTrace_matrix (v : Coordinates) :
    LinearMap.toMatrix' (unpackTrace v).val = unpack v :=
  LinearMap.toMatrix'_toLin' _

theorem coordinateAction_apply (c : Code) (v : Coordinates) :
    coordinateAction c v = pack (upperMatrix (codeBits c) *
      (if codeOuter c then reverseMatrix * (unpack v).transpose * reverseMatrix else unpack v) *
        upperInverse (codeBits c)) := by
  change coordinateEquiv (normalizerRepresentation adjoint (codeActor c)
    (mkAdjoint (unpackTrace v))) = _
  unfold codeActor
  split_ifs with ho
  · rw [map_mul]
    change coordinateEquiv (normalizerRepresentation adjoint (innerActor _)
      (normalizerRepresentation adjoint reversingGraphActor (mkAdjoint (unpackTrace v)))) = _
    rw [reversingGraphActor_mk, innerActor_mk, coordinateEquiv_mk]
    simp only [matrix_traceAction, traceTranspose_val, endTranspose_matrix,
      unpackTrace_matrix, reverseElement_inv, upperElement_inv]
    rfl
  · change coordinateEquiv (normalizerRepresentation adjoint (innerActor _)
      (mkAdjoint (unpackTrace v))) = _
    rw [innerActor_mk, coordinateEquiv_mk]
    simp only [matrix_traceAction, unpackTrace_matrix, upperElement_inv]
    rfl

theorem coordinateAction_matrix (c : Code) : LinearMap.toMatrix' (coordinateAction c) = actMatrix c := by
  ext i j
  simp only [LinearMap.toMatrix'_apply, coordinateAction_apply, actMatrix]

@[simp] theorem actMatrix_mulVec (c : Code) (v : Coordinates) :
    actMatrix c *ᵥ v = coordinateEquiv (normalizerRepresentation adjoint (codeActor c)
      (coordinateEquiv.symm v)) := by
  rw [← coordinateAction_matrix]
  exact LinearMap.toMatrix'_mulVec _ _


end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.FixedBounds
