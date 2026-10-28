module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.BlockModels.Planes
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.BlockModels.Alternating
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.BlockModels.G2
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry

/-!
# The V₂-plane marking for the two block coefficient models

For A₆ we reuse the actual natural-module flag geometry: the T₀-invariant
plane is the syntheme plane. For G₂(2)' we use the image of the first two
null octonion coordinates. Both planes have binary dimension two, and the
two detecting cubic elements stabilize them in the same coefficient action.
Their orders put them in O^{3′} of the actual subspace stabilizer.

These are marked model calculations for the centralizing branch of
Aschbacher--Smith 15.3.31, printed p.1132, using I.1.5--6 (p.408) and
the line geometry of I.2.3 (p.413). The G₂ cocycle result retains the concrete
pair-generation premise of the existing binary cocycle bound.
-/

@[expose] public section
open Subgroup Representation Representation.OneCohomology
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover.BlockModels

namespace Alternating
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry

/-- The syntheme plane in the actual four-dimensional natural section. -/
abbrev markedPlane := canonicalPlane

theorem markedPlane_finrank : Module.finrank (ZMod 2) markedPlane = 2 :=
  canonicalPlane_finrank

/-- Membership of the two detecting cubics in the actual line stabilizer. -/
theorem cubics_stabilize_markedPlane :
    cubicOne ∈ planeStabilizer action markedPlane ∧
    cubicTwo ∈ planeStabilizer action markedPlane := by
  constructor
  · apply (mem_planeStabilizer_iff_map action markedPlane cubicOne).mpr
    exact (canonicalPlane_stabilizer cubicOne.val).mpr (by decide +kernel)
  · apply (mem_planeStabilizer_iff_map action markedPlane cubicTwo).mpr
    exact (canonicalPlane_stabilizer cubicTwo.val).mpr (by decide +kernel)

/-- The source line marking detects all cocycles after taking O^{3′}. -/
theorem detectedOn_markedPlane_residual :
    DetectedOn action ((primeToResidual 3 (planeStabilizer action markedPlane)).map
      (planeStabilizer action markedPlane).subtype) :=
  detectedOn_residual_of_cubics _ cubics_stabilize_markedPlane.1 cubics_stabilize_markedPlane.2

/-- An actual two-dimensional T₀-invariant V₂ gives the same detection
without assuming in advance that its coordinates are the canonical plane. -/
theorem detectedOn_invariantPlane_residual (W : Submodule (ZMod 2) Coefficients)
    (hdim : Module.finrank (ZMod 2) W = 2)
    (hW : ∀ g ∈ T0, W.map (BinaryPermutation.naturalRepresentation (Fin 6) g) = W) :
    DetectedOn action ((primeToResidual 3 (planeStabilizer action W)).map
      (planeStabilizer action W).subtype) := by
  rw [canonicalPlane_unique W hdim hW]
  exact detectedOn_markedPlane_residual

end Alternating

namespace G2
open Atlas.G2 Atlas.G2.Natural Atlas.SplitOctonion

/-- The trace-zero lift on the second null basis coordinate. -/
def firstRepresentative : TraceZero (ZMod 2) :=
  ⟨![0,1,0,0,0,0,0,0], by change trace _ = 0; decide +kernel⟩
/-- The trace-zero lift on the first null basis coordinate. -/
def secondRepresentative : TraceZero (ZMod 2) :=
  ⟨![1,0,0,0,0,0,0,0], by change trace _ = 0; decide +kernel⟩

def firstVector : Coefficients := mk (ZMod 2) firstRepresentative
def secondVector : Coefficients := mk (ZMod 2) secondRepresentative

/-- The natural plane is the image of the null octonion plane on coordinates 0,1. -/
def markedPlane : Submodule (ZMod 2) Coefficients := pairPlane firstVector secondVector

private theorem cubicOne_cycle :
    action cubicOne firstVector = secondVector ∧
    action cubicOne secondVector = firstVector + secondVector := by
  constructor
  · apply binaryCoordinates_injective (ZMod 2)
    change binaryCoordinates (ZMod 2) (derivedAction (ZMod 2) cubicOne (mk _ firstRepresentative)) = _
    rw [derivedAction_mk, binaryCoordinates_mk]
    change _ = binaryCoordinates (ZMod 2) (mk _ secondRepresentative)
    rw [binaryCoordinates_mk]
    decide +kernel
  · apply binaryCoordinates_injective (ZMod 2)
    change binaryCoordinates (ZMod 2) (derivedAction (ZMod 2) cubicOne (mk _ secondRepresentative)) = _
    rw [derivedAction_mk, binaryCoordinates_mk, map_add]
    change _ = binaryCoordinates (ZMod 2) (mk _ firstRepresentative) +
      binaryCoordinates (ZMod 2) (mk _ secondRepresentative)
    rw [binaryCoordinates_mk, binaryCoordinates_mk]
    decide +kernel

private theorem cubicTwo_cycle :
    action cubicTwo firstVector = secondVector ∧
    action cubicTwo secondVector = firstVector + secondVector := by
  constructor
  · apply binaryCoordinates_injective (ZMod 2)
    change binaryCoordinates (ZMod 2) (derivedAction (ZMod 2) cubicTwo (mk _ firstRepresentative)) = _
    rw [derivedAction_mk, binaryCoordinates_mk]
    change _ = binaryCoordinates (ZMod 2) (mk _ secondRepresentative)
    rw [binaryCoordinates_mk]
    decide +kernel
  · apply binaryCoordinates_injective (ZMod 2)
    change binaryCoordinates (ZMod 2) (derivedAction (ZMod 2) cubicTwo (mk _ secondRepresentative)) = _
    rw [derivedAction_mk, binaryCoordinates_mk, map_add]
    change _ = binaryCoordinates (ZMod 2) (mk _ firstRepresentative) +
      binaryCoordinates (ZMod 2) (mk _ secondRepresentative)
    rw [binaryCoordinates_mk, binaryCoordinates_mk]
    decide +kernel

private theorem firstVector_ne_zero : firstVector ≠ 0 := by
  intro h
  have he := congrArg (fun v => binaryCoordinates (ZMod 2) v 1) h
  change binaryCoordinates (ZMod 2) (mk _ firstRepresentative) 1 = _ at he
  rw [binaryCoordinates_mk, map_zero] at he
  norm_num [firstRepresentative] at he

/-- This is an actual two-dimensional coefficient subspace. -/
theorem markedPlane_finrank : Module.finrank (ZMod 2) markedPlane = 2 :=
  pairPlane_finrank_of_cycle action cubicOne _ _ cubicOne_cycle.1 cubicOne_cycle.2 firstVector_ne_zero

/-- The detecting cubics stabilize the marked V₂-line in the same natural action. -/
theorem cubics_stabilize_markedPlane :
    cubicOne ∈ planeStabilizer action markedPlane ∧
    cubicTwo ∈ planeStabilizer action markedPlane :=
  ⟨mem_planeStabilizer_of_pair_cycle action cubicOne cubicOne_cube _ _
      cubicOne_cycle.1 cubicOne_cycle.2,
    mem_planeStabilizer_of_pair_cycle action cubicTwo cubicTwo_cube _ _
      cubicTwo_cycle.1 cubicTwo_cycle.2⟩

/-- The source parabolic's O^{3′} residual detects the actual cocycle.
The remaining generation input is precisely that of the binary cohomology bound. -/
theorem detectedOn_markedPlane_residual
    (hgen : closure ({binaryA (ZMod 2), binaryB (ZMod 2)} : Set Actor) = ⊤) :
    DetectedOn action ((primeToResidual 3 (planeStabilizer action markedPlane)).map
      (planeStabilizer action markedPlane).subtype) :=
  detectedOn_residual_of_cubics hgen _
    cubics_stabilize_markedPlane.1 cubics_stabilize_markedPlane.2

end G2

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover.BlockModels
