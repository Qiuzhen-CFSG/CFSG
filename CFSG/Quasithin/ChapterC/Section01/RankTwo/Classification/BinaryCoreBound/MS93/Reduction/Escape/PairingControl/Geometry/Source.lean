module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Paths

/-!
# The selected path and normalizer span in MS93 (4.3.2)

The centralizer choice keeps the actual predecessor three steps before the
endpoint. The backward choice keeps the incident edge whose displacement
escapes the far kernel, and a moving neighbor on that edge. Its groups P and W
are the literal local normalizer and its conjugate span, rather than arbitrary
subgroups with the desired bounds.

These are intermediate output types, with no source-only constructors here.
The centralizer choice, the exclusion of b = 6, and the step-(6) bound remain
proof obligations of the geometric argument.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(4)--(6), pp.884--885.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry
variable {M : Type*} [Group M] {R : Subgroup M} {geometry : MS93.Geometry R}

/-- Source (4): the centralizer is inside the actual holomorph-vertex kernel. -/
structure CentralizerChoice (p : Counterexample geometry) where
  t : Vertex R
  before : Before p.a p.a' t 3
  centralizer_eq : Q R t ⊓ centralizer (radiusCommutator p.a p.a' : Set (FreeAmalgam R)) =
    Q R p.c

/-- The vertices alpha-1 and alpha-2 chosen immediately before (6). -/
structure BackwardChoice (p : Counterexample geometry) where
  edge : Vertex R
  back : Vertex R
  adjacent_start : Adjacent R p.a edge
  adjacent_back : Adjacent R back edge
  moving : back ∈ movingNeighbors geometry p.a
  escapes : ¬ edgeDisplacement p.a edge ≤ Q R p.a'

namespace BackwardChoice

/-- The normalizer is relative to G_alpha, not to the whole amalgam. -/
noncomputable def P {p : Counterexample geometry} (choice : BackwardChoice p) :
    Subgroup (FreeAmalgam R) :=
  stabilizer R p.a ⊓ normalizer (edgeDisplacement p.a choice.edge : Set (FreeAmalgam R))

/-- Source W = <V_(alpha-2)^P> V_alpha, represented by the subgroup join. -/
noncomputable def W {p : Counterexample geometry} (choice : BackwardChoice p) :
    Subgroup (FreeAmalgam R) :=
  NormalizerTransfer.conjugatesIn (V R choice.back) choice.P ⊔ V R p.a

end BackwardChoice
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry
