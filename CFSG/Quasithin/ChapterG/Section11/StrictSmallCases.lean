module

public import CFSG.Quasithin.ChapterG.Section11.SourceSmallCases
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictRank

/-!
# The small G.11.2 branches on the actual strict quotient

The dotted actor is the original point centralizer modulo the kernel of its
conjugation action on U/Z(U). The isotropic space and elementary actor are
the literal crossing images from 6.2.17. An element in that crossing image
whose moved space contains the marked point supplies G.11.1(3ii), with no
change of quotient or representation. The small-degree source theorem then
gives the printed G.11.2 alternative.

The strict-intersection owner supplies the G.10 hypothesis and the witness
from 6.2.16--18; this module closes its classification step when the degree
is at most four. Higher-degree recognition and elimination remain open.
Source: Aschbacher--Smith 6.2.18(2), printed p.690.
-/

public section
open Subgroup Module Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  (T L R : Subgroup G) (z d : G)
  [IsElementaryAbelian 2 (StrictVectorQuotient T L R z)]
  [IsElementaryAbelian 2 (strictCrossingImage T L R z d)]

/-- The literal small-degree application of 6.2.18(2). The crossing center
is a relative subgroup of the original crossing image, as in G.10.1. -/
theorem strict_conclusion_of_degree_le_four
    (B : LinearMap.BilinForm (ZMod 2) (Additive (StrictVectorQuotient T L R z)))
    (v : Additive (StrictVectorQuotient T L R z))
    (h : ChapterG.Section10.Hypothesis (strictRepresentation T L R z) B v
      (strictHatSpace T L R z (strictCrossingIntersection T L R z d))
      (strictCrossingImage T L R z d)
      ((strictCrossingCenterImage T L R z d).subgroupOf (strictCrossingImage T L R z d)))
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple
      (StrictActor T L R z)))
    (a : StrictActor T L R z) (ha : a ∈ strictCrossingImage T L R z d)
    (hr : finrank (ZMod 2) (RankTwo.movedSpace (strictRepresentation T L R z) a) ≤ 2)
    (hv : v ∈ RankTwo.movedSpace (strictRepresentation T L R z) a)
    (hd : finrank (ZMod 2) (Additive (StrictVectorQuotient T L R z)) ≤ 4) :
    ChapterG.Section11.Conclusion (strictRepresentation T L R z) B
      (strictCrossingImage T L R z d) :=
  ChapterG.Section11.conclusion_of_degree_le_four h cover ⟨a, ha, hr, hv⟩ hd

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
