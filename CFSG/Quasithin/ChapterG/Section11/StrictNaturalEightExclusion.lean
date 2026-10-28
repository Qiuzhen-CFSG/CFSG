module
public import CFSG.Quasithin.ChapterG.Section11.NaturalEightExclusion
public import CFSG.Quasithin.ChapterG.Section11.StrictNaturalExclusion

/-!
# The doubled A₈ exclusion on the strict quotient

The source SQTK cover forces the centralizer of a doubled natural A₆ or A₈
component orbit to have odd order. For A₈ this lowers the ambient two-rank
bound to four and contradicts G.10.2. The proper marked branch therefore
retains only doubled A₆. The solvable, whole marked and exchanged branches
remain explicit, with the original strict quotient and relative normality.

Source: Aschbacher--Smith A.1.31(1), G.11.7--8 and 6.2.18(2),
printed pp.27--28,366--368,690. Exhaustive G.11.2 recognition remains open.
-/

public section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  (T L R : Subgroup G) (z d : G)
  [IsElementaryAbelian 2 (StrictVectorQuotient T L R z)]
  [IsElementaryAbelian 2 (strictCrossingImage T L R z d)]

/-- The actual strict quotient satisfies the refined G.11 reduction, with
relative Sylow normality and the exact low-rank witness supplied explicitly. -/
theorem strict_conclusion_or_six_natural_component_reduction
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
    (S : Sylow 2 (StrictActor T L R z))
    (hSv : (S : Subgroup (StrictActor T L R z)) ≤
      ChapterG.Section10.pointCentralizer (strictRepresentation T L R z) v)
    (hXS : strictCrossingImage T L R z d ≤ S)
    (hXn : ((strictCrossingImage T L R z d).subgroupOf
      (S : Subgroup (StrictActor T L R z))).Normal) :
    ChapterG.Section11.Conclusion (strictRepresentation T L R z) B
      (strictCrossingImage T L R z d) ∨
      (IsIrreducible (strictRepresentation T L R z) ∧
        6 ≤ finrank (ZMod 2) (Additive (StrictVectorQuotient T L R z)) ∧
        ((Group.IsSolvable (StrictActor T L R z) ∧
            finrank (ZMod 2) (Additive (strictCrossingImage T L R z d)) = 2 ∧
            finrank (ZMod 2) (Additive (StrictVectorQuotient T L R z)) = 6) ∨
          (¬ Group.IsSolvable (StrictActor T L R z) ∧
            ChapterG.Section11.SixNaturalComponentReduction (strictRepresentation T L R z) B v
              (strictHatSpace T L R z (strictCrossingIntersection T L R z d))
              (strictCrossingImage T L R z d)))) :=
  ChapterG.Section11.conclusion_or_six_natural_component_reduction h cover ⟨a,ha,hr,hv⟩ ⟨S,hSv,hXS,hXn⟩


end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
