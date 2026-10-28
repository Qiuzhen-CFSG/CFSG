/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Sporadic/Conway2Geometry.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Sporadic.Conway2
public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalLinePrimitivity
public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalLineSigns

/-!
The orthogonal-line geometry of the actual Conway Co2 vector stabilizer.
The concrete local semidirect product and five suborbits give the primitive action.

Source: Gerald Höhn, `Atlas/Sporadic/Conway2Geometry.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace Atlas.Sporadic.Conway2
open Atlas.Codes Atlas.Lattices Atlas.Conway

abbrev LocalGroup := orthogonalLineStabilizer ((0,0),0) ((0,0),1)
abbrev MarkedPairGroup := Mathieu22PairModel ((0,0),0) ⟨((0,0),1),by change ((0,0),1) ≠ ((0,0),0); decide⟩
abbrev SignModule := GolayPairSetKernel ((0,0),0) ⟨((0,0),1),by change ((0,0),1) ≠ ((0,0),0); decide⟩

def basePoint : Points := distinguishedOrthogonalLine _ _ (by decide)

theorem full_point_stabilizer : MulAction.stabilizer Model basePoint = LocalGroup :=
  distinguishedOrthogonalLine_stabilizer _ _ (by decide)

theorem local_card : Nat.card LocalGroup = 908328960 :=
  orthogonalLineStabilizer_order _ _ (by decide)

def localSemidirectEquiv :
    GolayPairSetMonomialGroup ((0,0),0) ⟨((0,0),1),by change ((0,0),1) ≠ ((0,0),0); decide⟩ ≃* LocalGroup :=
  fullOrthogonalLineSemidirectEquiv _ _

def signs : Subgroup LocalGroup := orthogonalLineSigns _ ⟨((0,0),1),by change ((0,0),1) ≠ ((0,0),0); decide⟩

theorem signs_card : Nat.card signs = 1024 := orthogonalLineSigns_card ((0,0),0) ⟨((0,0),1),by change ((0,0),1) ≠ ((0,0),0); decide⟩

theorem signModule_rank : Module.finrank Bit SignModule = 10 :=
  golay_two_coordinate_kernel_finrank _ _ (by decide)

theorem signs_normal : signs.Normal := orthogonalLineSigns_normal ((0,0),0) ⟨((0,0),1),by change ((0,0),1) ≠ ((0,0),0); decide⟩

theorem signs_commute (g h : signs) : g*h = h*g := orthogonalLineSigns_commute ((0,0),0) ⟨((0,0),1),by change ((0,0),1) ≠ ((0,0),0); decide⟩ g h

def pairProjection : LocalGroup →* MarkedPairGroup := orthogonalLinePairProjection ((0,0),0) ⟨((0,0),1),by change ((0,0),1) ≠ ((0,0),0); decide⟩
def pairSection : MarkedPairGroup →* LocalGroup := orthogonalLinePairSection ((0,0),0) ⟨((0,0),1),by change ((0,0),1) ≠ ((0,0),0); decide⟩

theorem pairProjection_kernel : pairProjection.ker = signs := orthogonalLinePairProjection_kernel ((0,0),0) ⟨((0,0),1),by change ((0,0),1) ≠ ((0,0),0); decide⟩

theorem pairProjection_section (g : MarkedPairGroup) : pairProjection (pairSection g) = g :=
  orthogonalLinePairProjection_section ((0,0),0) ⟨((0,0),1),by change ((0,0),1) ≠ ((0,0),0); decide⟩ g

def suborbitIndex : Points → Fin 5 := orthogonalLineIndex ((0,0),0) ((0,0),1)

theorem suborbit_card (t : Fin 5) :
    Nat.card {l : Points // suborbitIndex l = t} = ![1,462,21120,2464,22528] t :=
  orthogonalLine_fiber_card _ _ (by decide) t

theorem suborbit_transitive (l m : Points) (h : suborbitIndex l = suborbitIndex m) :
    ∃ g : MulAction.stabilizer Model basePoint, g • l = m :=
  orthogonalLine_index_transitive _ _ (by decide) l m h

theorem primitive : MulAction.IsPreprimitive Model Points :=
  orthogonalMinimumLines_primitive _ _ (by decide)

end Atlas.Sporadic.Conway2
