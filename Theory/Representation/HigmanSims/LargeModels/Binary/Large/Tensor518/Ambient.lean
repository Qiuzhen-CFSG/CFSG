module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Descent
public import Theory.Representation.HigmanSims.Twenty.Marked
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# The actual tensor of the marked degree-20 and degree-56 HS actions

We transport `Representation.tprod` through the product of the two standard
bases and flatten `(i,j)` to `56*i+j`. Thus the degree-56 index varies fastest.
The generator equations are the literal Kronecker matrices, with neither a
transpose nor an inverse. Both input actions are actions of the same HS
permutation carrier, so this construction requires no presentation or
unproved carrier identification.

The basis calculation follows Mathlib's `TensorProduct.toMatrix_map`
(Mathlib, Apache-2.0), proved locally to avoid an unavailable dependency artifact.
The source matrices and conventions are documented in `Binary/source/README.md`.
-/

@[expose] public section
open scoped TensorProduct Kronecker
namespace Representation.HigmanSims.LargeModels.Binary.Large.Tensor518
open Sporadic.LeechRelated.HS

def tensorMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin m) (ZMod 2))
    (B : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Matrix (Fin (m * n)) (Fin (m * n)) (ZMod 2) :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ B)

theorem tensorMatrix_apply {m n : ℕ} (A : Matrix (Fin m) (Fin m) (ZMod 2))
    (B : Matrix (Fin n) (Fin n) (ZMod 2)) (i j : Fin (m * n)) :
    tensorMatrix A B i j = A i.divNat j.divNat * B i.modNat j.modNat := rfl

noncomputable def tensorBasis (m n : ℕ) :=
  (Pi.basisFun (ZMod 2) (Fin m)).tensorProduct (Pi.basisFun (ZMod 2) (Fin n))

theorem tensorBasis_matrix {m n : ℕ}
    (f : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (g : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) :
    LinearMap.toMatrix (tensorBasis m n) (tensorBasis m n) (TensorProduct.map f g) =
      LinearMap.toMatrix' f ⊗ₖ LinearMap.toMatrix' g := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  simp only [tensorBasis, Matrix.kroneckerMap_apply, LinearMap.toMatrix_apply,
    Module.Basis.tensorProduct_apply, TensorProduct.map_tmul,
    Module.Basis.tensorProduct_repr_tmul_apply]
  simp only [Pi.basisFun_apply, Pi.basisFun_repr, smul_eq_mul, LinearMap.toMatrix'_apply]
  exact mul_comm _ _

noncomputable def coordinateAction {m n : ℕ}
    (ρ : Representation (ZMod 2) Carrier (Fin m → ZMod 2))
    (τ : Representation (ZMod 2) Carrier (Fin n → ZMod 2)) :
    Representation (ZMod 2) Carrier (Fin (m * n) → ZMod 2) :=
  Matrix.toLinAlgEquiv'.toAlgHom.toMonoidHom.comp
    ((Matrix.reindexRingEquiv (ZMod 2) finProdFinEquiv).toMonoidHom.comp
      ((LinearMap.toMatrixAlgEquiv (tensorBasis m n)).toAlgHom.toMonoidHom.comp
        (ρ.tprod τ)))

theorem coordinateAction_matrix {m n : ℕ}
    (ρ : Representation (ZMod 2) Carrier (Fin m → ZMod 2))
    (τ : Representation (ZMod 2) Carrier (Fin n → ZMod 2)) (g : Carrier) :
    LinearMap.toMatrix' (coordinateAction ρ τ g) =
      tensorMatrix (LinearMap.toMatrix' (ρ g)) (LinearMap.toMatrix' (τ g)) := by
  change LinearMap.toMatrixAlgEquiv' (Matrix.toLinAlgEquiv'
    (Matrix.reindex finProdFinEquiv finProdFinEquiv
      (LinearMap.toMatrix (tensorBasis m n) (tensorBasis m n)
        (TensorProduct.map (ρ g) (τ g))))) = _
  rw [LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv', tensorBasis_matrix]
  rfl

abbrev AmbientVector := Fin 1120 → ZMod 2
abbrev AmbientMatrix := Matrix (Fin 1120) (Fin 1120) (ZMod 2)

noncomputable def ambientAction (C20 : Twenty.MarkedComparison) (C56 : MarkedAction 0) :
    Representation (ZMod 2) Carrier AmbientVector := coordinateAction C20.action C56.action

theorem ambientAction_matrix (C20 : Twenty.MarkedComparison) (C56 : MarkedAction 0)
    (g : Carrier) :
    LinearMap.toMatrix' (ambientAction C20 C56 g) =
      tensorMatrix (LinearMap.toMatrix' (C20.action g))
        (LinearMap.toMatrix' (C56.action g)) :=
  coordinateAction_matrix C20.action C56.action g

theorem comparison_matrix_a (C20 : Twenty.MarkedComparison) :
    LinearMap.toMatrix' (C20.action permutationA) = Twenty.aMatrix := by
  change LinearMap.toMatrixAlgEquiv' (Twenty.representation (C20.hom Twenty.permutationA)) = _
  rw [C20.map_a]
  exact LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' _

theorem comparison_matrix_b (C20 : Twenty.MarkedComparison) :
    LinearMap.toMatrix' (C20.action permutationB) = Twenty.bMatrix := by
  change LinearMap.toMatrixAlgEquiv' (Twenty.representation (C20.hom Twenty.permutationB)) = _
  rw [C20.map_b]
  exact LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' _

def ambientA : AmbientMatrix := tensorMatrix Twenty.aMatrix (aMatrix 0)
def ambientB : AmbientMatrix := tensorMatrix Twenty.bMatrix (bMatrix 0)

theorem ambientAction_matrix_a (C20 : Twenty.MarkedComparison) (C56 : MarkedAction 0) :
    LinearMap.toMatrix' (ambientAction C20 C56 permutationA) = ambientA := (ambientAction_matrix C20 C56 _).trans
    (congrArg₂ tensorMatrix (comparison_matrix_a C20) C56.matrix_a)

theorem ambientAction_matrix_b (C20 : Twenty.MarkedComparison) (C56 : MarkedAction 0) :
    LinearMap.toMatrix' (ambientAction C20 C56 permutationB) = ambientB := (ambientAction_matrix C20 C56 _).trans
    (congrArg₂ tensorMatrix (comparison_matrix_b C20) C56.matrix_b)

end Representation.HigmanSims.LargeModels.Binary.Large.Tensor518
