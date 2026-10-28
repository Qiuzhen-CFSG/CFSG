module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Source

/-!
# The local generation statement used in the centralizer selection

For an M-vertex c and an incident H-vertex t, retain precisely the neighbors
s of c for which C_(Q_t)([Z_c,Q_s]) = Q_c. The displayed generation identity
immediately before MS93 (4.3.2)(4) says that their V-layers generate V_c.

This module defines that subgroup and the missing local-generation contract;
it does not assume or prove that the contract follows from the source inputs.
The selection assembly uses it to construct an actual new critical endpoint.

Source: Meierfrankenfeld--Stellmacher (1993), printed p.884.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer
variable {M : Type*} [Group M] {R : Subgroup M}

/-- The literal neighbor-generated subgroup in the display preceding (4). -/
noncomputable def centralizingNeighborSpan (c t : Vertex R) : Subgroup (FreeAmalgam R) :=
  ⨆ s, ⨆ (_ : Adjacent R c s),
    ⨆ (_ : Q R t ⊓ centralizer (edgeDisplacement c s : Set (FreeAmalgam R)) = Q R c),
      V R s

/-- The nontrivial inclusion of the source's local generation identity.
The opposite inclusion follows just from the neighboring balls. -/
def NeighborGeneration (R : Subgroup M) : Prop :=
  ∀ c t : Vertex R, color R c = false → Adjacent R c t →
    V R c ≤ centralizingNeighborSpan c t

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer
