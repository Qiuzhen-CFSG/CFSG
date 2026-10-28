module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.Inputs
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.Data

/-!
# Independent certificates for the degree-sixteen construction

The action certificate interprets the two explicit matrices as an action of
the actual native projective group. The density certificate is a calculation
in the matrix algebra, independent of the group law. Their assembly gives
irreducibility. Neither certificate asserts an arbitrary degree classification
or assumes that the requested four modules already exist.

These are outstanding proof contracts. `Data` contains their shared numerical
matrices and ATLAS attribution. The assembly owner must discharge both before
claiming `SixteenModelsExist` (GM02, Proposition 4.2, manuscript pp.9–10).
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels
universe v

/-- The action has precisely the marked generator matrices on the native group. -/
@[expose] def Realizes {F : Type*} [Field F] (t : F)
    (ρ : Representation F Matrix.PSL3Three.PSL (Fin 16 → F)) : Prop :=
  LinearMap.toMatrix' (ρ generatorA) = matrixA t ∧
  LinearMap.toMatrix' (ρ generatorB) = matrixB t

/-- Construct a genuine action with the two prescribed generator matrices.
The source group is the literal matrix quotient, not an ATLAS family label. -/
@[expose] def ActionsExist : Prop :=
  ∀ (F : Type v) [Field F] [CharP F 2], ∀ t : F, t ^ 4 = t + 1 →
    ∃ ρ : Representation F Matrix.PSL3Three.PSL (Fin 16 → F), Realizes t ρ

/-- The two explicit matrices generate the entire matrix algebra. This
certificate can be checked without constructing a group action. -/
@[expose] def GeneratorDensity : Prop :=
  ∀ (F : Type v) [Field F] [CharP F 2], ∀ t : F, t ^ 4 = t + 1 →
    Algebra.adjoin F ({matrixA t, matrixB t} : Set (Matrix (Fin 16) (Fin 16) F)) = ⊤

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels
