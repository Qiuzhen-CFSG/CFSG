module

public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.FirstCohomologyLinearTransport
public import Theory.Combinatorics.ProjectivePlaneMatrixAction
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.RepresentationTheory.Intertwining

/-!+# Concrete actions for the two SL₃ alternatives in G.9.3

The natural binary action is restriction of scalars of the column action.
The second coordinate action is inverse transpose, and the dot-product
equivalence below identifies it with the actual dual over the coefficient
field. The twisted tensor is the tensor of the natural action with its
entrywise field twist. None of these definitions asserts exhaustiveness
or descent to the fixed field.

Source: Aschbacher--Smith, G.9.3(8),(17), printed p.354; GLS III,
2.8.6, 2.8.8 and 2.8.10(c).
-/

@[expose] public section

open Representation
open scoped MatrixGroups TensorProduct

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition

variable (F : Type*) [Field F]

/-- The natural action after embedding the matrix-entry field in a splitting field. -/
def naturalOver {K : Type*} [Field K] (ι : F →+* K) :
    Representation K SL(3,F) (Fin 3 → K) :=
  (specialLinearNatural 3).comp (Matrix.SpecialLinearGroup.map ι)

/-- A tensor of two specified field conjugates over a splitting field. -/
noncomputable def twistedTensorOver {K : Type*} [Field K]
    (ι : F →+* K) (σ : F ≃+* F) :
    Representation K SL(3,F) ((Fin 3 → K) ⊗[K] (Fin 3 → K)) :=
  (naturalOver F ι).tprod (naturalOver F (ι.comp σ.toRingHom))

/-- The literal tensor product `N ⊗ N^σ` over the matrix-entry field. -/
noncomputable def twistedTensor (σ : F ≃+* F) :
    Representation F SL(3,F) ((Fin 3 → F) ⊗[F] (Fin 3 → F)) :=
  (specialLinearNatural 3).tprod
    ((specialLinearNatural 3).comp (Matrix.SpecialLinearGroup.map σ.toRingHom))

variable [Algebra (ZMod 2) F]

/-- Restriction of the natural three-dimensional action to the binary field. -/
def naturalBinary : Representation (ZMod 2) SL(3,F) (Fin 3 → F) :=
  restrictScalars (specialLinearNatural 3)

/-- The dual natural action in column coordinates. -/
def dualBinary : Representation (ZMod 2) SL(3,F) (Fin 3 → F) :=
  (naturalBinary F).comp Matrix.SpecialLinearGroup.inverseTranspose

/-- The coordinate dual is the genuine F-linear dual, restricted to F₂. -/
def dualBinaryEquiv : (dualBinary F).Equiv
    (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3).dual) :=
  .mk ((dotProductEquiv F (Fin 3)).restrictScalars (ZMod 2)) (by
    intro g
    apply LinearMap.ext
    intro w
    apply LinearMap.ext
    intro v
    change ((g⁻¹).val.transpose.mulVec w) ⬝ᵥ v = w ⬝ᵥ ((g⁻¹).val.mulVec v)
    rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec])

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
