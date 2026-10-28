module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Interface
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Density20.Certificate

/-!
# Absolute simplicity of the degree-20 middle factor

A checked straight-line program in the two fixed binary matrices produces a
rank-one outer product. Its left column orbit and right row orbit each span
20 dimensions, as certified by explicit inverses. The rank-one density criterion
therefore gives the full matrix algebra. Density survives scalar extension to
any field of characteristic two, and the upper coordinates give simplicity of
the literal augmentation quotient.

This discharges the degree-20 density input to the SU₃(5) principal-series
calculation motivated by Guralnick–Malle, Classification of 2F-modules I,
Proposition 4.3, and Aschbacher–Smith K.2, printed p.453. The construction of
`Coordinates` and the degree-104 density are separate inputs to the parent
assembly; neither is required for this fixed matrix-algebra theorem.
-/

public section

namespace Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors
open Thompson.BinaryMatrix CycleCertificate
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
open Density20Certificate

attribute [local irreducible] values leftIndex rightIndex column row columns rows
  columnInverse rowInverse

/-- The two degree-20 binary actors generate the entire matrix algebra. -/
theorem binary_density_20 : BinaryDensity factor20 := by
  intro Q h
  have hcr : Matrix.vecMulVec (fun i : Fin 20 => bit column i.val)
      (fun i : Fin 20 => bit row i.val) ∈ Q := by
    rw [← rank_one]
    exact value_mem Q h 30 (by decide)
  have hL (i : Fin 20) : decode 20 values[leftIndex i]! ∈ Q :=
    value_mem Q h _ (leftIndex_lt i)
  have hR (i : Fin 20) : decode 20 values[rightIndex i]! ∈ Q :=
    value_mem Q h _ (rightIndex_lt i)
  exact density_of_rank_one Q (fun i : Fin 20 => bit column i.val)
    (fun i : Fin 20 => bit row i.val) hcr
    (fun i => decode 20 values[leftIndex i]!)
    (fun i => decode 20 values[rightIndex i]!) hL hR
    (decode 20 columns) (decode 20 columnInverse) (decode 20 rows) (decode 20 rowInverse)
    columns_inverse rows_inverse left_action right_action

/-- Full matrix-algebra density after arbitrary characteristic-two scalar extension. -/
theorem factor20_density_charTwo (K : Type*) [Field K] [CharP K 2]
    (Q : Subalgebra K (Matrix (Fin 20) (Fin 20) K))
    (h : ∀ j, castMatrix K (factor20 j) ∈ Q) : Q = ⊤ :=
  density_cast K factor20 binary_density_20 Q h

/-- The literal upper quotient is simple over any characteristic-two field.
The only remaining input is its geometric coordinate realization. -/
theorem Coordinates.upper_isIrreducible {K : Type*} [Field K] [CharP K 2]
    (c : Coordinates K) :
    IsIrreducible (within c.space augmentationKernel).quotientRepresentation := by
  apply irreducible_of_coordinate_matrices (by decide) c.actors
    (fun j => castMatrix K (factor20 j)) c.upper c.upper_action
  exact factor20_density_charTwo K

end Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors
