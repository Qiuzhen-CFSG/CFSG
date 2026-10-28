module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.TraceEightWitness.InvariantRoots.OrbitChain
public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalPairGeometry

/-!
# Coordinate geometry for extending cubic root chains

The first two cubic orbits have the Gram matrix of a scaled D₄ lattice.
An isometry placing that marked lattice in four coordinate positions reduces
chain extension to elementary short-shell geometry. For the last step the
third orbit consists of a two-coordinate vector and an octad vector. The
remaining three positions in that octad provide the extension.

`D4FramePlacement` and `NormalizedThirdOrbitCompletion` are explicit geometric
obligations, not asserted theorems. Their consumer is
`cubicChainExtension_of_coordinate_geometry` in the parent module.

Source context: Aschbacher, *Sporadic Groups* (1994), 22.13 for the short
coordinate shapes and 25.1–25.5 for octad lattices. The marked D₄ reduction is
an additional argument; Chapter 9 Exercise 6 does not assert it.
-/

open Atlas.Lattices Atlas.Codes Atlas.Conway
open scoped BigOperators
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.TraceEightWitness.ChainExtension

@[expose] public noncomputable section

/-- Four coordinate positions in the first tetrad. -/
def frameCoordinate (i : Fin 4) : Omega := ((0, 0), i)

/-- The marked scaled D₄ configuration, in the order x₀,x₁,rx₀,rx₁. -/
def standardD4 : Fin 4 → leech :=
  ![minimumPairPlus (frameCoordinate 0) (frameCoordinate 1),
    minimumPairMinus (frameCoordinate 0) (frameCoordinate 1),
    minimumPairMinus (frameCoordinate 2) (frameCoordinate 1),
    minimumPairMinus (frameCoordinate 3) (frameCoordinate 0)]

/-- Integral pairing, i.e. raw coordinate dot product divided by eight. -/
def d4Gram : Matrix (Fin 4) (Fin 4) ℤ :=
  !![4,0,-2,-2; 0,4,2,-2; -2,2,4,0; -2,-2,0,4]

structure D4Configuration where
  root : Fin 4 → leech
  gram : ∀ i j, leechIntegralPairing (root i) (root j) = d4Gram i j

/-- Placement of a marked scaled D₄ lattice, with all four signs retained. -/
def D4FramePlacement : Prop :=
  ∀ f : D4Configuration, ∃ g : LeechIsometryGroup,
    ∀ i, g.val (f.root i) = standardD4 i

/-- The two short vectors beyond the standard D₄ frame admit a further neighbor.
This contract has no cubic action as an input. -/
def NormalizedThirdOrbitCompletion : Prop :=
  ∀ v w : leech, integerDot v.val v.val = 32 → integerDot w.val w.val = 32 →
    (∀ i, leechIntegralPairing (standardD4 i) v = if i = 3 then 2 else 0) →
    (∀ i, leechIntegralPairing (standardD4 i) w = if i = 1 then -2 else 0) →
    leechIntegralPairing v w = -2 →
    ∃ y : leech, integerDot y.val y.val = 32 ∧
      (∀ i, leechIntegralPairing (standardD4 i) y = 0) ∧
      leechIntegralPairing v y = 0 ∧ leechIntegralPairing w y = 2

/-- The next orbit after a standard D₄ frame starts with this coordinate pair. -/
def standardNeighbor : leech := minimumPairPlus (frameCoordinate 3) ((0, 1), 0)

theorem standardNeighbor_norm :
    integerDot standardNeighbor.val standardNeighbor.val = 32 :=
  minimumPairPlus_norm _ _ (by decide)

theorem standardNeighbor_pairing (i : Fin 4) :
    leechIntegralPairing (standardD4 i) standardNeighbor = if i = 3 then 2 else 0 := by
  fin_cases i <;>
    simp only [standardD4, standardNeighbor, leechIntegralPairing,
      minimumPairPlus, minimumPairMinus, integerDot_add_right, integerDot_coordinateVector] <;>
    norm_num [frameCoordinate, coordinateVector, Pi.single_apply, Fin.ext_iff]

end
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.TraceEightWitness.ChainExtension
