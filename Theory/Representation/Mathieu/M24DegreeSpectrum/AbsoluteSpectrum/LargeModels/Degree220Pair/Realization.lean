module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.BinaryModels
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Data

/-!
# Native realization and density contracts for the degree-220 pair

The native generators are the concrete permutations used to define the Witt
design. `Realizes` specifies their literal matrices in the standard coordinate
basis. Its existence must be proved, including any presentation or carrier
comparison needed to descend the matrix action to this group.

The independent density obligation concerns only the four explicit matrices.
The assembly in `Degree220Pair` transports density to absolute irreducibility
and uses the checked trace of the common native word to separate the actions.
Neither obligation is asserted here.

Sources: James, J. Algebra 27 (1973), 57–111; the ATLAS matrix data attributed
in `Degree220Pair/Data.lean`. These are construction contracts for the larger
models used with GM02 Proposition 5.1, manuscript p.17.
-/

@[expose] public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair
open Sporadic.Mathieu

/-- The actual first standard permutation, acting on the Witt design. -/
def generatorA : M24 := ⟨m24GeneratorA, m24GeneratorA_mem⟩

/-- The actual second standard permutation, with Lean's composition convention. -/
def generatorB : M24 := ⟨m24GeneratorB, m24GeneratorB_mem⟩

/-- Agreement at the two marked native elements; no irreducibility premise. -/
def Realizes (second : Bool) (ρ : Representation (ZMod 2) M24 (Fin 220 → ZMod 2)) :
    Prop :=
  LinearMap.toMatrix' (ρ generatorA) = matrixA second ∧
    LinearMap.toMatrix' (ρ generatorB) = matrixB second

/-- Realize both literal pairs on the native carrier, with their common marking. -/
def NativeRealizationsExist : Prop :=
  ∃ ρ : Bool → Representation (ZMod 2) M24 (Fin 220 → ZMod 2),
    ∀ second, Realizes second (ρ second)

/-- A concrete finite matrix-algebra generation obligation for each pair. -/
def MatrixAlgebrasFull : Prop :=
  ∀ second, Algebra.adjoin (ZMod 2)
    ({matrixA second, matrixB second} : Set (Matrix (Fin 220) (Fin 220) (ZMod 2))) = ⊤

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair
