module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The swap on the tensor square of a binary three-space

We identify the actual tensor product with three-by-three matrices, with
`x ⊗ y` having entry `x i * y j`. Factor interchange is matrix transpose.
Its displacement consists of symmetric matrices with zero diagonal. The
three off-diagonal entries give independent coordinates, and its fixed
space is the direct sum of this displacement and the diagonal matrices.
This proves moved dimension three and fixed dimension six without a large
finite computation. The two general linear factors act through the actual
tensor-product equivalence, and interchange conjugates their actions.

Source: Aschbacher–Smith, The Classification of Quasithin Groups, combined
manuscript of 1 March 2004, H.4.8(1,5), printed p.383. The finite generated
group and its source application are in the companion Group module.
-/

@[expose] public section

open scoped TensorProduct
namespace BinaryTensorThree

abbrev Natural := Fin 3 → ZMod 2
abbrev Space := Matrix (Fin 3) (Fin 3) (ZMod 2)
abbrev Tensor := Natural ⊗[ZMod 2] Natural
abbrev Factor := Natural ≃ₗ[ZMod 2] Natural

noncomputable def coordinates : Tensor ≃ₗ[ZMod 2] Space :=
  (TensorProduct.comm (ZMod 2) Natural Natural).trans
    (TensorProduct.piScalarRight (ZMod 2) (ZMod 2) Natural (Fin 3))

theorem coordinates_tmul (x y : Natural) (i j : Fin 3) :
    coordinates (x ⊗ₜ[ZMod 2] y) i j = x i * y j := by
  change (TensorProduct.piScalarRight (ZMod 2) (ZMod 2) Natural (Fin 3))
    (y ⊗ₜ[ZMod 2] x) i j = _
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  rfl

def flip : Space ≃ₗ[ZMod 2] Space where
  toFun := Matrix.transpose
  invFun := Matrix.transpose
  left_inv := Matrix.transpose_transpose
  right_inv := Matrix.transpose_transpose
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem flip_apply (v : Space) (i j : Fin 3) : flip v i j = v j i := rfl

@[simp] theorem flip_linearMap_apply (v : Space) : flip.toLinearMap v = flip v := rfl

theorem coordinates_swap (z : Tensor) :
    coordinates (TensorProduct.comm (ZMod 2) Natural Natural z) = flip (coordinates z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => ext i j; simp [coordinates_tmul, mul_comm]
  | add x y hx hy => simp [hx, hy]

noncomputable def baseAction : Factor × Factor →* (Space ≃ₗ[ZMod 2] Space) where
  toFun g := coordinates.symm.trans ((TensorProduct.congr g.1 g.2).trans coordinates)
  map_one' := by
    have h : TensorProduct.congr (1 : Factor) (1 : Factor) = LinearEquiv.refl (ZMod 2) Tensor := by
      exact TensorProduct.congr_refl_refl
    ext z
    simp [h]
  map_mul' g h := by ext z; simp [TensorProduct.congr_mul]

theorem baseAction_tmul (g : Factor × Factor) (x y : Natural) :
    baseAction g (coordinates (x ⊗ₜ[ZMod 2] y)) =
      coordinates (g.1 x ⊗ₜ[ZMod 2] g.2 y) := by simp [baseAction]

theorem flip_baseAction (g : Factor × Factor) (v : Space) :
    flip (baseAction g v) = baseAction (g.2, g.1) (flip v) := by
  obtain ⟨z, rfl⟩ := coordinates.surjective v
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [baseAction_tmul, ← coordinates_swap, TensorProduct.comm_tmul,
      ← coordinates_swap, TensorProduct.comm_tmul, baseAction_tmul]
  | add x y hx hy => simp [hx, hy]

def alternating : Natural →ₗ[ZMod 2] Space where
  toFun a := !![0, a 0, a 1; a 0, 0, a 2; a 1, a 2, 0]
  map_add' a b := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_smul' c a := by ext i j; fin_cases i <;> fin_cases j <;> simp

def diagonal : Natural →ₗ[ZMod 2] Space where
  toFun a := !![a 0, 0, 0; 0, a 1, 0; 0, 0, a 2]
  map_add' a b := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_smul' c a := by ext i j; fin_cases i <;> fin_cases j <;> simp

theorem alternating_injective : Function.Injective alternating := by
  intro a b h
  have h0 := congrArg (fun v : Space => v 0 1) h
  have h1 := congrArg (fun v : Space => v 0 2) h
  have h2 := congrArg (fun v : Space => v 1 2) h
  ext i
  fin_cases i <;> assumption

theorem displacement_range :
    LinearMap.range (flip.toLinearMap - LinearMap.id) = LinearMap.range alternating := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨![w 1 0 + w 0 1, w 2 0 + w 0 2, w 2 1 + w 1 2], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [alternating, CharTwo.sub_eq_add] <;> ring
  · rintro ⟨a, rfl⟩
    refine ⟨!![0, a 0, a 1; 0, 0, a 2; 0, 0, 0], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [alternating, CharTwo.sub_eq_add]

theorem finrank_displacement :
    Module.finrank (ZMod 2) (LinearMap.range (flip.toLinearMap - LinearMap.id)) = 3 := by
  rw [displacement_range, LinearMap.finrank_range_of_inj alternating_injective]
  simp

theorem fixed_decomposition :
    LinearMap.ker (flip.toLinearMap - LinearMap.id) =
      LinearMap.range alternating ⊔ LinearMap.range diagonal := by
  ext v
  constructor
  · intro hv
    have hs : flip v = v := sub_eq_zero.mp hv
    have h01 := congrArg (fun w : Space => w 0 1) hs
    have h02 := congrArg (fun w : Space => w 0 2) hs
    have h12 := congrArg (fun w : Space => w 1 2) hs
    apply Submodule.mem_sup.mpr
    refine ⟨alternating ![v 0 1, v 0 2, v 1 2], ⟨_, rfl⟩,
      diagonal ![v 0 0, v 1 1, v 2 2], ⟨_, rfl⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all [alternating, diagonal]
  · intro hv
    obtain ⟨a, ⟨x, rfl⟩, b, ⟨y, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hv
    change flip (alternating x + diagonal y) - (alternating x + diagonal y) = 0
    apply sub_eq_zero.mpr
    ext i j
    fin_cases i <;> fin_cases j <;> simp [alternating, diagonal]

theorem displacement_disjoint_diagonal :
    Disjoint (LinearMap.range alternating) (LinearMap.range diagonal) := by
  apply Submodule.disjoint_def.mpr
  rintro v ⟨a, rfl⟩ ⟨b, h⟩
  have h0 := congrArg (fun v : Space => v 0 1) h
  have h1 := congrArg (fun v : Space => v 0 2) h
  have h2 := congrArg (fun v : Space => v 1 2) h
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all [alternating, diagonal]

theorem finrank_fixed :
    Module.finrank (ZMod 2) (LinearMap.ker (flip.toLinearMap - LinearMap.id)) = 6 := by
  have h := (flip.toLinearMap - LinearMap.id).finrank_range_add_finrank_ker
  rw [finrank_displacement] at h
  have hd : Module.finrank (ZMod 2) Space = 9 := by
    rw [Module.finrank_matrix]
    norm_num
  omega

end BinaryTensorThree
