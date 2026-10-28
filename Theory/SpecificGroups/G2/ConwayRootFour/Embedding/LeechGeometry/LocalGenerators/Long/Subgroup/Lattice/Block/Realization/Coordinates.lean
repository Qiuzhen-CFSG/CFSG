module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.MatrixData
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Descent

/-!
# A faithful rational quaternion action of the Eisenstein block

Embed the Eisenstein root as left multiplication by `(-1+i+j+k)/2` on
rational Hamilton quaternions. Expanding all six coordinates is faithful.
The inverse adjoint turns the source ROW Gram identity `A H A* = H` into
a genuine left action preserving the column form with Gram matrix `2 H`.

This module constructs the rational action only. The integral lattice and
its comparison with the retained Leech carrier are separate obligations.
Matrix source: John Bray, ATLAS `6L34G1-Ar6aB0`, as transcribed and checked
in `Block.MatrixData`. The quaternion expansion here is an explicit construction.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Matrix Atlas.Algebra
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization

abbrev Index := Fin 6 × Fin 4
abbrev Space := Index → ℚ
abbrev RealMatrix := Matrix Index Index ℚ

/-- Left multiplication by (-1+i+j+k)/2 on rational Hamilton quaternions. -/
def omegaMatrix : Matrix (Fin 4) (Fin 4) ℚ :=
  (1/2 : ℚ) • !![-1,-1,-1,-1;1,-1,-1,1;1,1,-1,-1;1,-1,1,-1]

def scalarRealification : Eisenstein →+* Matrix (Fin 4) (Fin 4) ℚ :=
  (QuadraticAlgebra.lift ⟨omegaMatrix, by decide +kernel⟩).toRingHom

theorem scalarRealification_apply (z : Eisenstein) :
    scalarRealification z = z.re • (1 : Matrix (Fin 4) (Fin 4) ℚ) +
      z.im • omegaMatrix := rfl

theorem scalarRealification_injective : Function.Injective scalarRealification := by
  intro x y h
  have h0 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℚ => M 0 0) h
  have h1 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℚ => M 1 0) h
  simp [scalarRealification_apply, omegaMatrix, Matrix.intCast_apply] at h0 h1
  have hr : x.re = y.re := by
    simpa [h1] using h0
  exact QuadraticAlgebra.ext hr h1

/-- Expand each Eisenstein entry to its faithful rational quaternion block. -/
def realification : SixMatrix →+* RealMatrix where
  toFun A i j := scalarRealification (A i.1 j.1) i.2 j.2
  map_zero' := by ext i j; simp
  map_one' := by
    ext ⟨i,k⟩ ⟨j,l⟩
    by_cases h : i=j
    · subst j; simp [Matrix.one_apply]
    · simp [h]
  map_add' A B := by ext i j; simp [Matrix.add_apply]
  map_mul' A B := by
    ext ⟨i,k⟩ ⟨j,l⟩
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.sum_apply]

theorem realification_injective : Function.Injective realification := by
  intro A B h
  apply Matrix.ext
  intro i j
  apply scalarRealification_injective
  ext k l
  exact congrArg (fun M : RealMatrix => M (i,k) (j,l)) h

theorem scalarRealification_star (z : Eisenstein) :
    scalarRealification (star z) = (scalarRealification z).transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarRealification_apply, omegaMatrix, Matrix.intCast_apply, Matrix.transpose_apply] <;> ring

theorem realification_conjTranspose (A : SixMatrix) :
    realification A.conjTranspose = (realification A).transpose := by
  ext ⟨i,k⟩ ⟨j,l⟩
  exact congrArg (fun M : Matrix (Fin 4) (Fin 4) ℚ => M k l)
    (scalarRealification_star (A j i))

/-- Inverse adjoint converts the source row-Gram convention to a left action. -/
def columnAction : GL (Fin 6) Eisenstein →* GL (Fin 6) Eisenstein where
  toFun g := ⟨g.inv.conjTranspose, g.val.conjTranspose, by
    rw [← Matrix.conjTranspose_mul, g.val_inv, Matrix.conjTranspose_one], by
    rw [← Matrix.conjTranspose_mul, g.inv_val, Matrix.conjTranspose_one]⟩
  map_one' := by apply Units.ext; exact Matrix.conjTranspose_one
  map_mul' g h := by apply Units.ext; exact Matrix.conjTranspose_mul _ _

theorem columnAction_injective : Function.Injective columnAction := by
  intro g h he
  have hv := congrArg (fun u : GL (Fin 6) Eisenstein => u.val.conjTranspose) he
  have hi : g⁻¹ = h⁻¹ := Units.ext (by simpa [columnAction] using hv)
  exact inv_injective hi

/-- Faithful rational expansion on the ambient general linear group. -/
def rationalMatrices : GL (Fin 6) Eisenstein →* GL Index ℚ :=
  (Units.map realification.toMonoidHom).comp columnAction

/-- The literal degree-24 rational action of the matrix group. -/
def rationalAction : matrixGroup →* GL Index ℚ :=
  rationalMatrices.comp matrixGroup.subtype

theorem rationalAction_injective : Function.Injective rationalAction := by
  intro g h he
  apply Subtype.ext
  apply columnAction_injective
  apply Units.ext
  apply realification_injective
  exact congrArg Units.val he

def gramMatrix : RealMatrix := (2 : ℚ) • realification hermitianMatrix

/-- The rational bilinear form in the six quaternion coordinates. -/
def form (x y : Space) : ℚ := dotProduct x (gramMatrix *ᵥ y)

def linearMatrices : GL Index ℚ ≃* (Space ≃ₗ[ℚ] Space) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv ℚ Space)

@[simp] theorem linearMatrices_apply (g : GL Index ℚ) (x : Space) :
    linearMatrices g x = g.val *ᵥ x := rfl

def linearAction : matrixGroup →* (Space ≃ₗ[ℚ] Space) :=
  linearMatrices.toMonoidHom.comp rationalAction

theorem linearAction_injective : Function.Injective linearAction :=
  linearMatrices.injective.comp rationalAction_injective

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization
