module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.FactorSimplicity.Density84.Orbits
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.FactorSimplicity.Assembly

/-!
# Full matrix-algebra density on the cubic 84-dimensional middle quotient

The exact two quotient matrices contain a checked rank-one operator in their
coefficient-field algebra. Both its column and row orbits contain checked
bases. The rank-one criterion therefore proves full matrix-algebra density,
not merely irreducibility over the four-element coefficient field. The
existing coordinate and scalar-extension assembly applies this result to the
literal middle quotient of the principal-series flag over every supplied
cubic scalar.

The final corollary leaves only the independent image-density premise. Its
unconditional discharge belongs to the joint factor-certificate assembly.
Source motivation: Guralnick–Malle Proposition 4.3, p.10;
Aschbacher–Smith K.2, p.453. The finite witnesses and measured checking costs
are documented in `Density84/source/README.md`.
-/

@[expose] public section
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates
open CubicCalculation.FactorSimplicity Certificate.Packed
universe v

/-- The fixed matrices on the literal 84-dimensional middle quotient generate
its entire matrix algebra over the cubic coefficient field. -/
theorem middle_density : MatrixDensity middleMatrices := by
  intro Q hG
  apply Density84.density_of_orbits middleMatrices
    (matrix 84 Density84.cols) (matrix 84 Density84.rows)
    Density84.cp Density84.rp Density84.ca Density84.ra
    Density84.column_parents Density84.row_parents
    Density84.column_recurrence Density84.row_recurrence
    Density84.column_span Density84.row_span Q hG
  change Matrix.vecMulVec (Density84.vector (Density84.cols 0))
    (Density84.vector (Density84.rows 0)) ∈ Q
  rw [← Density84.rank_one]
  exact Density84.p85_mem Q hG

/-- Apply middle density to the literal quotient certificates; only the
independent density calculation for the 21-dimensional image remains. -/
theorem modelCertificates_of_image_density (hi : MatrixDensity imageMatrices) :
    ModelCertificates.{v} :=
  modelCertificates_of_density hi middle_density

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates
