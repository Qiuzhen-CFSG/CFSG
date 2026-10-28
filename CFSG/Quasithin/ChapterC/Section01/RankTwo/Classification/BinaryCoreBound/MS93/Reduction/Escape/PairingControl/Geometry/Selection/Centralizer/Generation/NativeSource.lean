module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.Coordinates
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Native dual vectors at incident edges

The two coordinates use the same marked quotient: U_c has its natural
matrix action, and Vcirc_c/U_c has the inverse-transpose action. A native
lift realizes a dual vector inside V_s for an actual neighbor s of c,
and that vector annihilates the actual displacement [Z_c,Q_s].

This is a geometric proof obligation, not an assertion that an arbitrary
pair of opposite modules supplies native lifts. It mentions neither the
selected-neighbor span nor a centralizer-selected critical endpoint.
The generation assembly discharges all further linear-algebra and relative
centralizer steps from these lifts.

Source: Meierfrankenfeld--Stellmacher (1993), the local generation display
before (4.3.2)(4), printed p.884.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation
variable {M : Type*} [Group M] {R : Subgroup M}

/-- The evaluation pairing for the actual natural and dual coordinates. -/
def pairing (v u : Space) : ZMod 2 := dotProduct v.toAdd u.toAdd

/-- A dual vector realized by a native neighboring radius group, with the
natural displacement plane in its annihilator. -/
structure NativeNeighborLift {c : Vertex R} (o : OppositeSectionAt c)
    (hC : Vcirc R c ≤ stabilizer R c) (v : Space) where
  neighbor : Vertex R
  adjacent : Adjacent R c neighbor
  vector : Vcirc R c
  in_neighbor : (vector : FreeAmalgam R) ∈ V R neighbor
  coordinates : movingCoordinates o hC vector = v
  annihilates : ∀ d : U R c, (d : FreeAmalgam R) ∈ edgeDisplacement c neighbor →
    pairing v (naturalEquiv o d) = 0

/-- Uniform realization of the nonzero dual vectors. This is a remaining
source-geometric target; its construction is not part of this definition. -/
def NativeNeighborLifts {c : Vertex R} (o : OppositeSectionAt c)
    (hC : Vcirc R c ≤ stabilizer R c) : Prop :=
  ∀ v : Space, v ≠ 1 → Nonempty (NativeNeighborLift o hC v)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation
