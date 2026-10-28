module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Suzuki.Recognition
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Suzuki.Quotient
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Suzuki.Fixed
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Suzuki.Coordinates
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Suzuki.Diagonal
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Suzuki.FixedAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Suzuki.OrbitAction

/-!
# Suzuki component detection: recognition and quotient lifting

Even original field degree supplies a genuine Suzuki quotient by the full
K-group classification. Independently of that parity, a marked Suzuki
orbit Borel with its field action and normalizer lifts gives the shared
BorelMovement on the original Geometry. This application verifies the
placement of the entire orbit in Y using only relative normality in G₁.

OrbitAction constructs the coordinates and field actor from the actual Suzuki
quotient for both fixed and swapped component orbits. Diagonal supplies all
normalizer lifts. Thus only the genuine preceding flag/Cartan inputs remain;
no invariant torus or field-action conclusion is assumed.
Source: Aschbacher--Smith 11.5.6(3), printed pp.780--781.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open CartanActions.FieldDetection.Suzuki
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Relative normality retains the entire original T-orbit inside Y. -/
theorem suzuki_orbit_le_Y (hT : (T : Subgroup G) ≤ E.G₁)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I) : orbit T I ≤ E.Y :=
  conjugateSpanBy_le hI.1 (hT.trans E.G₁_normalizes_Y)

/-- Actual source application of quotient detection, valid for either
parity of the original field degree and for both component orbits. -/
theorem suzuki_borel_movement_of_coordinates (hT : (T : Subgroup G) ≤ E.G₁)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I) {m : ℕ} (hm : 0 < m)
    (c : OrbitCoordinates T I m) (a : FieldAction E c hm)
    (hlift : c.NormalizerLifts hm) : E.BorelMovement :=
  a.borel_movement (E.suzuki_orbit_le_Y hT hI) hlift

/-- In the fixed-component branch the normalizer calculation introduces
no extra premise beyond the constructed field coordinates. -/
theorem suzuki_borel_movement_of_fixed (hT : (T : Subgroup G) ≤ E.G₁)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (hTI : (T : Subgroup G) ≤ normalizer (I : Set G)) {m : ℕ} (hm : 0 < m)
    (c : OrbitCoordinates T I m) (a : FieldAction E c hm) : E.BorelMovement :=
  E.suzuki_borel_movement_of_coordinates hT hI hm c a
    (c.normalizerLifts_of_fixed hm hTI)

/-- Fixed-component Borel movement after the marked quotient and actor have
been supplied.  This is the original consumer of the coordinate constructor. -/
theorem suzuki_borel_movement_of_fixed_marked
    (hT : (T : Subgroup G) ≤ E.G₁)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (hTI : (T : Subgroup G) ≤ normalizer (I : Set G))
    {m : ℕ} (hm : 0 < m)
    (e : (I ⧸ pCore 2 I) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hroot : ((T : Subgroup G).subgroupOf I).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))) =
      BenderSuzuki.MatrixGroups.SuzukiRootSubgroup m)
    (a : FieldAction E (orbitCoordinates_of_fixed hTI hm e hroot) hm) :
    E.BorelMovement := by
  exact E.suzuki_borel_movement_of_fixed hT hI hTI hm
    (orbitCoordinates_of_fixed hTI hm e hroot) a

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
