module
public import Theory.Representation.G2NaturalBinary
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.Generators
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.Data
/-!
# Natural matrices for the binary parabolic-filtration generators

Lift six off-diagonal coordinates to trace-zero octonions with both diagonal
coordinates zero. Checking the two actual root-word actors on the six basis
vectors computes their induced matrices on the quotient by the identity line.
Linearity then proves the formulas for every vector.

The actors and their right-coset convention come from the attributed ATLAS
port in `VertexFiltrations.Generators` (see LICENSES/ATLAS.txt). These formulas
connect its finite simple factors to the natural action required in
Aschbacher--Smith G.9.3(10), printed pp.354,356--357.
-/

@[expose] public section
namespace G2DerivedSixFactorMaps
open G2DerivedPermutationFiltration.VertexCoordinates
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
open Atlas.G2.Natural Atlas.G2.Natural.Binary

private def lift : Six →ₗ[ZMod 2] Atlas.SplitOctonion.Carrier (ZMod 2) where
  toFun v := ![v 0, v 1, v 2, 0, 0, v 3, v 4, v 5]
  map_add' _ _ := by ext r; fin_cases r <;> simp
  map_smul' _ _ := by ext r; fin_cases r <;> simp

private def liftTrace : Six →ₗ[ZMod 2] TraceZero (ZMod 2) :=
  lift.codRestrict _ (by intro v; change (0 : ZMod 2) + 0 = 0; rfl)

private theorem coordinates_lift (v : Six) :
    coordinatesEquiv (mk (ZMod 2) (liftTrace v)) = v := by
  change binaryOffDiagonal (ZMod 2) (lift v) = v
  ext r; fin_cases r <;> rfl

/-- Matrices of the actual parabolic-filtration generator pair on the six natural coordinates. -/
def naturalRows : Fin 2 → Fin 6 → ℕ :=
  ![![40,26,58,29,13,52], ![58,40,37,50,11,39]]

def naturalMatrix (j : Fin 2) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  fun r s => bit (naturalRows j r) s.val

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem generator_basis : ∀ (j : Fin 2) (b : Fin 6) (a : ZMod 2),
    binaryOffDiagonal (ZMod 2) ((groupGenerator j).val.val (lift (Pi.single b a))) =
      (naturalMatrix j).mulVec (Pi.single b a) := by
  decide +kernel

private theorem generator_lift (j : Fin 2) (v : Six) :
    binaryOffDiagonal (ZMod 2) ((groupGenerator j).val.val (lift v)) =
      (naturalMatrix j).mulVec v := by
  have h : (binaryOffDiagonal (ZMod 2)).comp
      ((groupGenerator j).val.val.toLinearMap.comp lift) = (naturalMatrix j).toLin' := by
    apply LinearMap.pi_ext
    exact generator_basis j
  exact LinearMap.congr_fun h v

/-- Natural coordinates intertwine the entire literal action of each certified generator. -/
theorem natural_generator (j : Fin 2) (v : Six) :
    coordinateAction (groupGenerator j) v = (naturalMatrix j).mulVec v := by
  have h := coordinatesEquiv_action (groupGenerator j) (mk (ZMod 2) (liftTrace v))
  rw [coordinates_lift] at h
  rw [← h, derivedAction_mk]
  exact generator_lift j v
end G2DerivedSixFactorMaps
