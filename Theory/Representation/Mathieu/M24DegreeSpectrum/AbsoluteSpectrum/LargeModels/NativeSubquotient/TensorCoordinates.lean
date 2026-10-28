module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native120.Code
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.KernelAbsolute
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Native tensor coordinates for the large Mathieu constituents

The code coordinates and the nonzero exterior-kernel comparison construct
native actions of dimensions 11 and 44. Density proves the latter comparison
injective. Kronecker products and inverse transposes then give honest native
actions of dimensions 484, 1936 and 2420, in the row-major tensor order used
by the saved subquotient witnesses. No presentation comparison is required.

Source: James, J. Algebra 27 (1973), 57–111; GM02 Proposition 5.1.
The degree-220 matrices retain the attribution in Degree220Pair/source/README.md.
-/

@[expose] public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.TensorCoordinates
open Sporadic.Mathieu
open scoped Kronecker
open Degree220Pair
open SmallModels.FortyFour

private def preserving (W : Submodule (ZMod 2) KernelAbsolute.Data.Space) :
    Subalgebra (ZMod 2) KernelAbsolute.Data.Mat where
  carrier := {M | ∀ x ∈ W, M.mulVec x ∈ W}
  zero_mem' := by intro x _; simp
  one_mem' := by intro x hx; simpa using hx
  add_mem' := by
    intro M N hM hN x hx
    simpa only [Matrix.add_mulVec] using W.add_mem (hM x hx) (hN x hx)
  mul_mem' := by
    intro M N hM hN x hx
    simpa only [← Matrix.mulVec_mulVec] using hM _ (hN x hx)
  algebraMap_mem' := by
    intro r x hx
    simpa only [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
      using W.smul_mem r hx

/-- Density certifies the rank of the existing native comparison without a
new numerical inverse. -/
theorem kernel_comparison_injective : Function.Injective KernelAbsolute.NativeMap.comparisonMap := by
  let T := KernelAbsolute.NativeMap.comparisonMap
  have hfull : preserving T.ker = ⊤ := by
    apply KernelAbsolute.Density.full
    intro j x hx
    change T ((KernelAbsolute.Data.matrix j).mulVec x) = 0
    have hx' : KernelAbsolute.NativeMap.comparisonMap x = 0 := hx
    exact (KernelAbsolute.NativeMap.comparisonMap_action j x).trans
      ((congrArg (SmallModels.FortyFour.kernelRepresentation (KernelAbsolute.nativeGenerator j)) hx').trans
        (map_zero _))
  apply LinearMap.ker_eq_bot.mp
  by_contra hn
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hz
    push Not at hz
    exact hx0 (funext hz)
  have hi1 : x i = 1 := by
    have hb : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
    exact (hb (x i)).resolve_left hi
  apply KernelAbsolute.NativeMap.comparisonMap_ne_zero
  apply LinearMap.ext
  intro y
  have hm : Matrix.vecMulVec y (Pi.single i 1) ∈ preserving T.ker := by
    rw [hfull]
    trivial
  have hy := hm x hx
  simpa [Matrix.vecMulVec_mulVec, hi1] using hy

/-- The literal 44-dimensional column matrices act on native M24. -/
theorem kernel_action_exists :
    ∃ ρ : Representation (ZMod 2) M24 KernelAbsolute.Data.Space,
      LinearMap.toMatrix' (ρ generatorA) = KernelAbsolute.Data.matrix 0 ∧
      LinearMap.toMatrix' (ρ generatorB) = KernelAbsolute.Data.matrix 1 := by
  apply of_embedding SmallModels.FortyFour.kernelRepresentation _ _
    KernelAbsolute.NativeMap.comparisonMap kernel_comparison_injective
  · apply LinearMap.ext
    intro v
    exact (KernelAbsolute.NativeMap.comparisonMap_action 0 v).symm
  · apply LinearMap.ext
    intro v
    exact (KernelAbsolute.NativeMap.comparisonMap_action 1 v).symm

def kernelAction : Representation (ZMod 2) M24 KernelAbsolute.Data.Space :=
  kernel_action_exists.choose

theorem kernelAction_first : LinearMap.toMatrix' (kernelAction generatorA) = KernelAbsolute.Data.matrix 0 :=
  kernel_action_exists.choose_spec.1

theorem kernelAction_second : LinearMap.toMatrix' (kernelAction generatorB) = KernelAbsolute.Data.matrix 1 :=
  kernel_action_exists.choose_spec.2

/-- Row-major tensor matrix: (i,j) has index i*n+j. -/
def tensorMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin m) (ZMod 2))
    (B : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Matrix (Fin (m*n)) (Fin (m*n)) (ZMod 2) :=
  Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) finProdFinEquiv (A ⊗ₖ B)

theorem tensorMatrix_apply {m n : ℕ} (A : Matrix (Fin m) (Fin m) (ZMod 2))
    (B : Matrix (Fin n) (Fin n) (ZMod 2)) (i j : Fin (m*n)) :
    tensorMatrix A B i j = A i.divNat j.divNat * B i.modNat j.modNat := rfl

/-- Tensor action constructed from two genuine native representations. -/
def tensorAction {m n : ℕ}
    (ρ : Representation (ZMod 2) M24 (Fin m → ZMod 2))
    (σ : Representation (ZMod 2) M24 (Fin n → ZMod 2)) :
    Representation (ZMod 2) M24 (Fin (m*n) → ZMod 2) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp
    { toFun g := tensorMatrix (LinearMap.toMatrix' (ρ g)) (LinearMap.toMatrix' (σ g))
      map_one' := by simp [tensorMatrix]
      map_mul' g h := by
        simp only [map_mul, LinearMap.toMatrix'_mul, tensorMatrix, Matrix.mul_kronecker_mul] }

theorem tensorAction_matrix {m n : ℕ}
    (ρ : Representation (ZMod 2) M24 (Fin m → ZMod 2))
    (σ : Representation (ZMod 2) M24 (Fin n → ZMod 2)) (g : M24) :
    LinearMap.toMatrix' (tensorAction ρ σ g) =
      tensorMatrix (LinearMap.toMatrix' (ρ g)) (LinearMap.toMatrix' (σ g)) :=
  LinearMap.toMatrix'_toLin' _

/-- Standard dual coordinates, with the inverse required for a left action. -/
def dualAction {n : ℕ} (ρ : Representation (ZMod 2) M24 (Fin n → ZMod 2)) :
    Representation (ZMod 2) M24 (Fin n → ZMod 2) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp
    { toFun g := (LinearMap.toMatrix' (ρ g⁻¹)).transpose
      map_one' := by simp
      map_mul' g h := by
        simp only [mul_inv_rev, map_mul, LinearMap.toMatrix'_mul, Matrix.transpose_mul] }

private theorem generatorA_inverse : generatorA⁻¹ = generatorA := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  change m24GeneratorA * m24GeneratorA = 1
  rw [← pow_two, ← m24GeneratorA_order, pow_orderOf_eq_one]

private theorem generatorB_inverse : generatorB⁻¹ = generatorB ^ 2 := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  change m24GeneratorB ^ 2 * m24GeneratorB = 1
  rw [← pow_succ]
  change m24GeneratorB ^ 3 = 1
  rw [← m24GeneratorB_order, pow_orderOf_eq_one]

theorem dualAction_first {n : ℕ} (ρ : Representation (ZMod 2) M24 (Fin n → ZMod 2)) :
    LinearMap.toMatrix' (dualAction ρ generatorA) =
      (LinearMap.toMatrix' (ρ generatorA)).transpose := by
  change LinearMap.toMatrix' (Matrix.toLin' _) = _
  rw [LinearMap.toMatrix'_toLin']
  change (LinearMap.toMatrix' (ρ generatorA⁻¹)).transpose = _
  rw [generatorA_inverse]

theorem dualAction_second {n : ℕ} (ρ : Representation (ZMod 2) M24 (Fin n → ZMod 2)) :
    LinearMap.toMatrix' (dualAction ρ generatorB) =
      (LinearMap.toMatrix' (ρ generatorB) ^ 2).transpose := by
  change LinearMap.toMatrix' (Matrix.toLin' _) = _
  rw [LinearMap.toMatrix'_toLin']
  change (LinearMap.toMatrix' (ρ generatorB⁻¹)).transpose = _
  rw [generatorB_inverse, map_pow]
  congr 1
  simp only [pow_two, LinearMap.toMatrix'_mul]

abbrev codeAction := Degrees120252.Native120.coordinateCodeRepresentation

def action484 : Representation (ZMod 2) M24 (Fin 484 → ZMod 2) :=
  tensorAction codeAction kernelAction

theorem action484_first : LinearMap.toMatrix' (action484 generatorA) =
    tensorMatrix (Degrees120252.Native120.codeMatrix 0) (KernelAbsolute.Data.matrix 0) := by
  rw [action484, tensorAction_matrix codeAction kernelAction, kernelAction_first]
  rw [show generatorA = Degrees120252.actor 0 from rfl,
    Degrees120252.Native120.coordinateCodeRepresentation_actor]

theorem action484_second : LinearMap.toMatrix' (action484 generatorB) =
    tensorMatrix (Degrees120252.Native120.codeMatrix 1) (KernelAbsolute.Data.matrix 1) := by
  rw [action484, tensorAction_matrix codeAction kernelAction, kernelAction_second]
  rw [show generatorB = Degrees120252.actor 1 from rfl,
    Degrees120252.Native120.coordinateCodeRepresentation_actor]

def action1936 : Representation (ZMod 2) M24 (Fin 1936 → ZMod 2) :=
  tensorAction kernelAction (dualAction kernelAction)

theorem action1936_first : LinearMap.toMatrix' (action1936 generatorA) =
    tensorMatrix (KernelAbsolute.Data.matrix 0) (KernelAbsolute.Data.matrix 0).transpose := by
  rw [action1936, tensorAction_matrix kernelAction (dualAction kernelAction), dualAction_first, kernelAction_first]

theorem action1936_second : LinearMap.toMatrix' (action1936 generatorB) =
    tensorMatrix (KernelAbsolute.Data.matrix 1) (KernelAbsolute.Data.matrix 1 ^ 2).transpose := by
  rw [action1936, tensorAction_matrix kernelAction (dualAction kernelAction), dualAction_second, kernelAction_second]

def action220b : Representation (ZMod 2) M24 (Fin 220 → ZMod 2) :=
  nativeRealizationsExist.choose true

theorem action220b_realizes : Realizes true action220b :=
  nativeRealizationsExist.choose_spec true

def action2420 : Representation (ZMod 2) M24 (Fin 2420 → ZMod 2) :=
  tensorAction codeAction action220b

theorem action2420_first : LinearMap.toMatrix' (action2420 generatorA) =
    tensorMatrix (Degrees120252.Native120.codeMatrix 0) (matrixA true) := by
  rw [action2420, tensorAction_matrix codeAction action220b, action220b_realizes.1]
  rw [show generatorA = Degrees120252.actor 0 from rfl,
    Degrees120252.Native120.coordinateCodeRepresentation_actor]

theorem action2420_second : LinearMap.toMatrix' (action2420 generatorB) =
    tensorMatrix (Degrees120252.Native120.codeMatrix 1) (matrixB true) := by
  rw [action2420, tensorAction_matrix codeAction action220b, action220b_realizes.2]
  rw [show generatorB = Degrees120252.actor 1 from rfl,
    Degrees120252.Native120.coordinateCodeRepresentation_actor]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.TensorCoordinates
