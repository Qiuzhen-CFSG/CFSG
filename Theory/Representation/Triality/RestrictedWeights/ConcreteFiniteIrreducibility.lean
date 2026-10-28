module

public import Theory.Representation.Triality.RestrictedWeights.ConcreteCellCoordinates
public import Theory.Representation.Triality.RestrictedWeights.ConcreteExtremalSpaces
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.SourceCharts.Concrete
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.LeftAssembly
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftContracts.FiniteHighest

/-!
# Actual restricted triality modules are irreducible on the finite group

The source PBW argument bounds the full extremal covariant spaces. Actual
root-chart coefficients and top divided-power nonvanishing give both finite
cell sums. The exact coordinate witnesses supply the cardinalities, so finite
interpolation detects highest lines and spans every restricted highest orbit.
The positive finite radical then proves irreducibility on the original group.
Only universality of the same Spin carrier remains as a shared geometric input.
Weight separation, exhaustion and the final FF assembly are separate consumers.
Source: Steinberg 13.2(d)–13.3(a), GLS3 2.8.2.
-/

public noncomputable section
open Theory.AlgebraicGroup
open Triality.SimplyConnected
open Triality.RestrictedWeights.SteinbergTensors FiniteRestriction
namespace Triality.RestrictedWeights.Concrete
universe u
variable (k:Type u) [Field k] [IsAlgClosed k] [CharP k 2]
variable (hu:IsUniversalVersion (groupVariety k))

/-- Exact finite interpolation of both extremal covariant spaces. -/
theorem leftExtremalCellInjectivity (n:ℕ) (hn:0<n) :
    LeftExtremalCellInjectivity (finiteGeometry k hu) n :=
  leftExtremalCellInjectivity_of_coordinates (finiteGeometry k hu) n hn
    (cellCoordinates k hu n hn) (leftDimensionBounds k hu n)
    (leftCellSums_of_coordinates k hu n hn (cellCoordinates k hu n hn))

/-- Complementary actual highest-weight sections give the entire restricted range. -/
theorem leftRestrictedCellInjectivity (n:ℕ) (hn:0<n) :
    LeftRestrictedCellInjectivity (finiteGeometry k hu) n :=
  leftRestrictedCellInjectivity_of_extremal_of_sections (finiteGeometry k hu) n
    (leftExtremalCellInjectivity k hu n hn) (complementarySections k hu n)

/-- Finite positive-radical invariants are exactly in the original highest line. -/
theorem leftFiniteHighestLine (n:ℕ) (hn:0<n) :
    LeftFiniteHighestLine (finiteGeometry k hu) n :=
  leftFiniteHighestLine_of_cellInjectivity (finiteGeometry k hu) n
    (leftRestrictedCellInjectivity k hu n hn)

/-- The literal finite highest-vector orbit spans the actual module. -/
theorem leftFiniteHighestOrbitSpan (n:ℕ) (hn:0<n) :
    LeftFiniteHighestOrbitSpan (finiteGeometry k hu) n :=
  leftFiniteHighestOrbitSpan_of_cellInjectivity (finiteGeometry k hu) n
    (leftRestrictedCellInjectivity k hu n hn)

/-- All actual restricted rational irreducibles remain irreducible after finite restriction. -/
theorem leftRestrictedIrreducibility (n:ℕ) (hn:0<n) :
    LeftRestrictedIrreducibility (finiteGeometry k hu) n :=
  leftRestrictedIrreducibility_of_finiteHighestLine_of_orbitSpan (finiteGeometry k hu) n hn
    (leftFiniteHighestLine k hu n hn) (leftFiniteHighestOrbitSpan k hu n hn)

end Triality.RestrictedWeights.Concrete
