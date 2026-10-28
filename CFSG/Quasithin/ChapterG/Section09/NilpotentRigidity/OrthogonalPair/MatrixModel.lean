/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Adapted from ATLAS, Atlas/LinearGroups/Orthogonal/D2MatrixAction.lean.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.Elementary
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.Forms
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.FinCases
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The determinant action for the binary orthogonal pair

The hyperbolic coordinates of `formD 2 F` identify it with the determinant
on two-by-two matrices. The two determinant-one factors act by
`M ↦ A M B⁻¹`. Over the binary field the displayed six matrices give the
actual action of `DihedralGroup 3`; composing the two factors gives
`pairHom`, an action on the precise quadratic space used by G.9.2.

The coordinate and general matrix-action proofs are adapted from
`Atlas/LinearGroups/Orthogonal/D2MatrixAction.lean`; imports, namespace and
isometry carrier are adapted to CFSG. The binary marking is explicit here.
Source application: Aschbacher--Smith G.9.2, printed pp.352--353,
`refs/quasithin.pdf`, PDF pp.363--364.
-/
@[expose] public noncomputable section
namespace ClassicalOrthogonal.BinaryD2
open Matrix
variable {F : Type*} [Field F]
abbrev Mat := Matrix (Fin 2) (Fin 2) F
abbrev PairSL := Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F

/-- The determinant coordinates retain the two ordered hyperbolic pairs. -/
def coordinates : VectorD 2 F ≃ₗ[F] Mat (F := F) where
  toFun v := !![v (.inl 0),v (.inl 1);-v (.inr 1),v (.inr 0)]
  invFun M := Sum.elim ![M 0 0,M 0 1] ![M 1 1,-M 1 0]
  left_inv v := by ext i; rcases i with i|i <;> fin_cases i <;> simp
  right_inv M := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_add' u v := by ext i j; fin_cases i <;> fin_cases j <;> simp [add_comm]
  map_smul' c v := by ext i j; fin_cases i <;> fin_cases j <;> simp

theorem coordinates_det (v : VectorD 2 F) : (coordinates v).det = formD 2 F v := by
  simp [coordinates,Matrix.det_fin_two,formD_apply,Fin.sum_univ_succ]

/-- The determinant quadratic form on the actual matrix space. -/
def determinantForm : QuadraticForm F (Mat (F := F)) :=
  (formD 2 F).comp coordinates.symm.toLinearMap

theorem determinantForm_apply (M : Mat (F := F)) : determinantForm M = M.det := by
  change formD 2 F (coordinates.symm M) = M.det
  exact (coordinates_det (coordinates.symm M)).symm.trans
    (congrArg Matrix.det (coordinates.apply_symm_apply M))

/-- The actual split quadratic space is isometric to two-by-two determinant space. -/
def coordinatesIsometry : (formD 2 F).IsometryEquiv (determinantForm (F := F)) where
  __ := coordinates
  map_app' v := by
    change formD 2 F (coordinates.symm (coordinates v)) = formD 2 F v
    rw [LinearEquiv.symm_apply_apply]

def matrixAction (g : PairSL (F := F)) : Mat (F := F) ≃ₗ[F] Mat (F := F) where
  toFun M := g.1.val * M * g.2⁻¹.val
  invFun M := g.1⁻¹.val * M * g.2.val
  left_inv M := by
    change g.1⁻¹.val * (g.1.val * M * g.2⁻¹.val) * g.2.val = M
    calc
      _ = (g.1⁻¹.val*g.1.val)*M*(g.2⁻¹.val*g.2.val) := by simp only [mul_assoc]
      _ = M := by rw [← SpecialLinearGroup.coe_mul,← SpecialLinearGroup.coe_mul,
        inv_mul_cancel,inv_mul_cancel,SpecialLinearGroup.coe_one,one_mul,mul_one]
  right_inv M := by
    change g.1.val * (g.1⁻¹.val * M * g.2.val) * g.2⁻¹.val = M
    calc
      _ = (g.1.val*g.1⁻¹.val)*M*(g.2.val*g.2⁻¹.val) := by simp only [mul_assoc]
      _ = M := by rw [← SpecialLinearGroup.coe_mul,← SpecialLinearGroup.coe_mul,
        mul_inv_cancel,mul_inv_cancel,SpecialLinearGroup.coe_one,one_mul,mul_one]
  map_add' M N := by simp [mul_add,add_mul]
  map_smul' c M := by simp

theorem matrixAction_det (g : PairSL (F := F)) (M : Mat (F := F)) :
    (matrixAction g M).det = M.det := by
  change (g.1.val*M*g.2⁻¹.val).det = _
  rw [Matrix.det_mul,Matrix.det_mul,g.1.det_coe,g.2⁻¹.det_coe,one_mul,mul_one]

def onD (g : PairSL (F := F)) : VectorD 2 F ≃ₗ[F] VectorD 2 F :=
  coordinates.trans ((matrixAction g).trans coordinates.symm)

theorem onD_form (g : PairSL (F := F)) (v : VectorD 2 F) :
    formD 2 F (onD g v) = formD 2 F v := by
  rw [← coordinates_det,← coordinates_det]
  change (coordinates (coordinates.symm (matrixAction g (coordinates v)))).det = _
  rw [LinearEquiv.apply_symm_apply,matrixAction_det]

def toOrthogonal : PairSL (F := F) →* Theory.AlgebraicGroup.quadraticIsometrySubgroup (formD 2 F) where
  toFun g := ⟨onD g, (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mpr (onD_form g)⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change coordinates.symm ((1 : SpecialLinearGroup (Fin 2) F).val * coordinates v *
      (1 : SpecialLinearGroup (Fin 2) F)⁻¹.val) = v
    rw [inv_one,SpecialLinearGroup.coe_one,one_mul,mul_one,LinearEquiv.symm_apply_apply]
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change coordinates.symm ((g.1*h.1).val*coordinates v*(g.2*h.2)⁻¹.val) =
      coordinates.symm (g.1.val*coordinates (coordinates.symm
        (h.1.val*coordinates v*h.2⁻¹.val))*g.2⁻¹.val)
    rw [LinearEquiv.apply_symm_apply,_root_.mul_inv_rev,SpecialLinearGroup.coe_mul,
      SpecialLinearGroup.coe_mul]
    simp only [mul_assoc]

theorem toOrthogonal_coordinates (g : PairSL (F := F)) (v : VectorD 2 F) :
    coordinates ((toOrthogonal g).val v) = g.1.val*coordinates v*g.2⁻¹.val :=
  coordinates.apply_symm_apply _


abbrev Pair := DihedralGroup 3 × DihedralGroup 3
abbrev Space := VectorD 2 (ZMod 2)

/-- Matrices for the standard rotation and reflection of the binary plane. -/
def planeMatrix : DihedralGroup 3 → Matrix (Fin 2) (Fin 2) (ZMod 2)
  | .r i => if i = 0 then 1 else if i = 1 then !![0, 1; 1, 1] else !![1, 1; 1, 0]
  | .sr i => if i = 0 then !![1, 1; 0, 1] else if i = 1 then !![1, 0; 1, 1]
      else !![0, 1; 1, 0]

theorem planeMatrix_det : ∀ g, (planeMatrix g).det = 1 := by decide +kernel

/-- The actual two-dimensional binary dihedral action in determinant-one matrices. -/
def planeHom : DihedralGroup 3 →* SpecialLinearGroup (Fin 2) (ZMod 2) where
  toFun g := ⟨planeMatrix g, planeMatrix_det g⟩
  map_one' := by apply Subtype.ext; rfl
  map_mul' := by
    have h : ∀ g h, planeMatrix (g * h) = planeMatrix g * planeMatrix h := by decide +kernel
    exact fun g k => Subtype.ext (h g k)

/-- The four-dimensional left-right action of the two dihedral factors. -/
def pairHom : Pair →* Theory.AlgebraicGroup.quadraticIsometrySubgroup (formD 2 (ZMod 2)) :=
  toOrthogonal.comp (planeHom.prodMap planeHom)

end ClassicalOrthogonal.BinaryD2
