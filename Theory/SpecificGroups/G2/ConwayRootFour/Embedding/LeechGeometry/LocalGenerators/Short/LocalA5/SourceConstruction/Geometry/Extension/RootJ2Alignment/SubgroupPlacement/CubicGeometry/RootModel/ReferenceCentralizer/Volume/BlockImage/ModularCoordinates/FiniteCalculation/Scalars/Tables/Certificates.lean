module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteCalculation.Transport

/-!
# Exact integer certificates for right Hurwitz multiplication

The three axis identities and the half-unit identity are checked over the integers
in the actual glued quaternion basis. Clearing denominators here keeps the costly
finite checks separate from their rational and modulo-two applications.

Derived from John Bray's ATLAS 6L34G1-Ar6aB0 matrices and Gerald Höhn's
icosian comparison; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Source consumer: Aschbacher, Sporadic Groups (1994), 49.5, pp.283–284.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Algebra Atlas.Lattices Atlas.Codes Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long
namespace ReferenceBlock.ModularCoordinates.FiniteCalculation.Scalars.TableCertificates
open Long.Block Long.Block.Realization

def rightInteger (a b c d : ℤ) : Matrix Index Index ℤ := fun i j =>
  if i.1 = j.1 then
    (!![a,-b,-c,-d;b,a,d,-c;c,-d,a,b;d,c,-b,a] : Matrix (Fin 4) (Fin 4) ℤ) i.2 j.2
  else 0

def rightAxisNumerator (k : Fin 3) : Matrix Index Index ℤ :=
  ![rightInteger 0 1 0 0, rightInteger 0 0 1 0, rightInteger 0 0 0 1] k

def rightAxis (k : Fin 3) : RealMatrix :=
  ![rightScalar 0 1 0 0, rightScalar 0 0 1 0, rightScalar 0 0 0 1] k

theorem axis_numerator : ∀ k, rightAxis k = integerMatrix (rightAxisNumerator k) := by
  decide +kernel

theorem axis_integer : ∀ k, rightAxisNumerator k * basisNumerator =
    basisNumerator * rightAxisTable k := by decide +kernel

theorem half_numerator : rightScalar (1/2) (1/2) (1/2) (1/2) =
    (1/2 : ℚ) • integerMatrix (rightInteger 1 1 1 1) := by decide +kernel

theorem half_integer : rightInteger 1 1 1 1 * basisNumerator =
    2 • (basisNumerator * rightHalfTable) := by decide +kernel

end ReferenceBlock.ModularCoordinates.FiniteCalculation.Scalars.TableCertificates
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
