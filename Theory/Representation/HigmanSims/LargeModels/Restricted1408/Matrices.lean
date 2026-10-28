module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.RowsA
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.RowsB
public import Theory.Representation.HigmanSims.LargeModels.Inputs
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.GeneratorCover
public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!+# The literal degree-1408 restriction matrices

The two binary matrices come from the ATLAS HS:2 candidate through the
published HS subgroup words. Matrix multiplication retains the source's
ordinary multiplication convention; neither a transpose nor an inverse is
applied to the resulting matrices. The permutation carrier, by contrast,
already inverts the source right-action permutations.

Two independent obligations remain: construct a representation of that
literal carrier with these generator images, and prove that the matrices
generate the full matrix algebra. Checking a presentation's relations does
not by itself solve the first obligation. Irreducibility of the HS:2 action
does not by itself solve the second. These are construction contracts, not
assertions that either obligation has been met.

Source: ATLAS HSd2G1-f2r1408B0 and HSd2G1-max1W1; original data, attribution
and the reproducible extraction are retained in `source/`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Restricted1408

open Sporadic.LeechRelated.HS

abbrev Vector := Fin 1408 → ZMod 2
abbrev Mat := Matrix (Fin 1408) (Fin 1408) (ZMod 2)

/-- The first restricted matrix, with entries in the published source order. -/
def matrixA : Mat := Thompson.BinaryMatrix.decode 1408 aRows

/-- The second restricted matrix, with entries in the published source order. -/
def matrixB : Mat := Thompson.BinaryMatrix.decode 1408 bRows

/-- Descent must identify the images of both literal permutation generators.
The source application may supply simplicity; no irreducibility is assumed. -/
def MatrixDescentExists : Prop :=
  IsSimpleGroup Carrier →
    ∃ ρ : Representation (ZMod 2) Carrier Vector,
      LinearMap.toMatrix' (ρ generatorAElement) = matrixA ∧
      LinearMap.toMatrix' (ρ generatorBElement) = matrixB

/-- A finite algebra certificate on the actual restricted pair. This is
independent of the construction of the permutation-carrier action. -/
def MatrixAlgebraIsFull : Prop :=
  Algebra.adjoin (ZMod 2) {matrixA, matrixB} = ⊤

end Representation.HigmanSims.LargeModels.Restricted1408
