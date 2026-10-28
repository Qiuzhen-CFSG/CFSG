module
public import Theory.Representation.HermitianTensorThree.PointSection.Transvections
public import Theory.SpecificGroups.PSL3.LinearThreeLocalCoordinates
public import Theory.Representation.SL2.BinarySmallModels
import all Theory.Representation.HermitianTensorThree.PointSection.Transvections

/-!
# The two point-local sections of the Hermitian nine-space

Conjugating the first-row coordinates identifies the five-space modulo its
central line with the natural module for the original lower Levi block.
The lower Hermitian corner is the quotient of the nine-space by that
five-space and carries the Hermitian action of the same block. Both maps
are surjective and their full kernels are computed explicitly.

The internal transvection import reuses the established row coordinates
without changing their public boundary. Source: Aschbacher–Smith H.4.6(4)
and 8.2.11(2–3), printed pp.382,722, refs/quasithin.pdf. The source extension
uses the actual field transport and five-point A₅ comparison.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.HermitianTensorThree.PointSection
set_option backward.isDefEq.respectTransparency false
local instance pointSectionBinarySMul : SMul (ZMod 2) (Space 1) := (binaryModule 1).toSMul
local instance pointSectionBinaryAlgebra : Algebra (ZMod 2) (F 1) := ZMod.algebra _ 2
local instance pointSectionBinaryModule : Module (ZMod 2) (OrthogonalFourMinus.FiniteModel.Space 1) :=
  Module.compHom _ (algebraMap (ZMod 2) (F 1))

/-- Conjugating the row coordinates makes the lower Levi block act naturally. -/
def conjugateRow : Space 1 →ₗ[ZMod 2] (Fin 2 → E 1) where
  toFun X i := sigma 1 (X.val 0 i.succ)
  map_add' X Y := by ext i; exact map_add _ _ _
  map_smul' a X := by fin_cases a <;> simp; rfl

/-- The lower Hermitian corner is the quotient by the point five-space. -/
def lowerCorner : Space 1 →ₗ[ZMod 2] OrthogonalFourMinus.FiniteModel.Space 1 where
  toFun X := ⟨fun i j => X.val i.succ j.succ,by
    ext i j
    exact entry_conjugate 1 X i.succ j.succ⟩
  map_add' X Y := rfl
  map_smul' a X := by fin_cases a <;> simp; rfl

theorem lowerCorner_surjective : Function.Surjective lowerCorner := by
  intro X
  let c := OrthogonalFourMinus.FiniteModel.coordinates 1 X
  refine ⟨(coordinates 1).symm (![0,c.1.1,c.1.2],![0,0,c.2]),?_⟩
  apply (OrthogonalFourMinus.FiniteModel.coordinates 1).injective
  rfl

theorem lowerCorner_kernel (X : Space 1) : lowerCorner X=0 ↔ X ∈ moved := by
  rw [mem_moved]
  constructor
  · intro h
    exact ⟨congrArg (fun x => x.val 0 0) h,congrArg (fun x => x.val 1 1) h,
      congrArg (fun x => x.val 0 1) h⟩
  · rintro ⟨h11,h22,h12⟩
    apply (OrthogonalFourMinus.FiniteModel.coordinates 1).injective
    apply Prod.ext
    · apply Prod.ext <;> apply Subtype.ext
      · exact h11
      · exact h22
    · exact h12

theorem conjugateRow_kernel (X : moved) : conjugateRow X.val=0 ↔ X.val ∈ line := by
  rw [←row_kernel]
  constructor
  · intro h
    ext i
    exact (sigma 1).injective ((congrFun h i).trans (map_zero _).symm)
  · intro h
    ext i
    change sigma 1 (row X i)=0
    rw [congrFun h i]
    exact map_zero (sigma 1)

theorem conjugateRow_surjective : ∀ v : Fin 2 → E 1,
    ∃ X : moved, conjugateRow X.val=v := by
  intro v
  refine ⟨movedCoordinates.symm (0,sigma 1 (v 0),sigma 1 (v 1)),?_⟩
  ext i
  fin_cases i <;> exact sigma_involutive 1 _

/-- Both genuine section actions use the same original lower Levi block. -/
theorem point_local_sections (a : Matrix.PSL3.LinearThree.pointLocalSL (E 1)) :
    let b := (Matrix.PSL3.LinearThree.pointLocalAffineEquiv (E 1) a).right
    (∀ X : moved,
      conjugateRow (binaryActionHom 1 a.val X.val) = b.val.mulVec (conjugateRow X.val)) ∧
    (∀ X : Space 1,
      lowerCorner (binaryActionHom 1 a.val X) = SL2.BinarySmall.hermitian 1 b (lowerCorner X)) := by
  dsimp only
  have ha := (Matrix.PSL3.LinearThree.mem_pointLocalSL_iff _ _).mp a.property
  have hs (t : E 1) : sigma 1 (sigma 1 t) = t := sigma_involutive 1 t
  have hb := Matrix.PSL3.LinearThree.pointLocalAffineEquiv_right_val (E 1) a
  constructor
  · intro X
    have hx := (mem_moved X.val).mp X.property
    have h21 : X.val.val 2 1=0 := by rw [←entry_conjugate 1 X.val 2 1,hx.2.2,map_zero]
    ext i
    change sigma 1 ((a.val.val * X.val.val * adjoint 1 a.val.val) 0 i.succ) = _
    rw [hb]
    fin_cases i <;>
      simp [conjugateRow,adjoint,Matrix.mul_apply,Fin.sum_univ_three,
        Matrix.mulVec,dotProduct,Fin.sum_univ_two,ha.1,ha.2.1,ha.2.2,hx.1,hx.2.1,hx.2.2,h21,
        map_add,map_mul,hs]
    all_goals ring
  · intro X
    apply Subtype.ext
    rw [SL2.BinarySmall.hermitian_apply,hb]
    ext i j
    change (a.val.val * X.val * adjoint 1 a.val.val) i.succ j.succ = _
    fin_cases i <;> fin_cases j <;>
      simp [lowerCorner,adjoint,OrthogonalFourMinus.adjoint,Matrix.mul_apply,
        Matrix.vecMul,dotProduct,Fin.sum_univ_three,Fin.sum_univ_two,ha.2.1,ha.2.2]

end Representation.HermitianTensorThree.PointSection
