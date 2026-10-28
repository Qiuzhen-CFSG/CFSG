module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.BinaryModels
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.Data
public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Native-action and density obligations for the degree-320 pair

The literal binary matrices are independent of the two remaining proofs:
their realization on the Witt-design group, and generation of the full matrix
algebra. The latter proves absolute irreducibility after the former is supplied.

ATLAS uses right actions, whereas Lean representations act on columns.
We therefore mark the inverses of the native ATLAS permutations: the raw
ATLAS matrices must be the images of these explicitly specified elements.
Neither matrix labels nor the two generator equations alone assert that the
action exists. See `source/README.md` for data provenance and the source use.
-/

@[expose] public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair
open Sporadic.Mathieu Thompson.BinaryMatrix

abbrev Space := Fin 320 → ZMod 2
abbrev Mat := Matrix (Fin 320) (Fin 320) (ZMod 2)

/-- First literal matrix; false labels ATLAS 320a, true labels ATLAS 320b. -/
def matrixA (variant : Bool) : Mat := decode 320 (if variant then Data.Ab else Data.Aa)

/-- Second literal matrix, with the same variant convention. -/
def matrixB (variant : Bool) : Mat := decode 320 (if variant then Data.Bb else Data.Ba)

/-- The inverse native first generator, for the raw ATLAS row-matrix convention. -/
def actorA : M24 := (⟨m24GeneratorA, m24GeneratorA_mem⟩ : M24)⁻¹

/-- The inverse native second generator, for the raw ATLAS row-matrix convention. -/
def actorB : M24 := (⟨m24GeneratorB, m24GeneratorB_mem⟩ : M24)⁻¹

/-- The raw matrices must act on these particular elements of native M24. -/
def Realizes (variant : Bool) (ρ : Representation (ZMod 2) M24 Space) : Prop :=
  LinearMap.toMatrix' (ρ actorA) = matrixA variant ∧
    LinearMap.toMatrix' (ρ actorB) = matrixB variant

/-- The carrier-comparison obligation; it contains no irreducibility premise. -/
def ActionsExist : Prop :=
  ∀ variant, ∃ ρ : Representation (ZMod 2) M24 Space, Realizes variant ρ

/-- A finite algebra-generation obligation, independent of the carrier comparison. -/
def GeneratorDensity : Prop :=
  ∀ variant, Algebra.adjoin (ZMod 2) ({matrixA variant, matrixB variant} : Set Mat) = ⊤

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair
