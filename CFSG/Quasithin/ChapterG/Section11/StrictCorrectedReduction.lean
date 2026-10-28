module
public import CFSG.Quasithin.ChapterG.Section11.CorrectedReduction
public import CFSG.Quasithin.ChapterG.Section11.StrictNaturalSixExclusion

/-!
# The corrected exchanged reduction on the original strict quotient

The actual strict action satisfies the corrected G.11 reduction: every
full-linear exchanged constituent now yields the marked whole S₈ action.
The original thirteen alternatives remain intact. The remaining solvable,
whole-component and nondegenerate natural exchanged branches are explicit.
No ambient exclusion or exhaustive catalogue premise is assumed here.

Source: Aschbacher--Smith G.11.1--7 and 6.2.18(2), printed pp.364--367,690,
with the G.10.15 full-four correction in `docs/quasithin-proof-basis.md`.
-/

public section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  (T L R : Subgroup G) (z d : G)
  [IsElementaryAbelian 2 (StrictVectorQuotient T L R z)]
  [IsElementaryAbelian 2 (strictCrossingImage T L R z d)]

/-- Application to the literal strict quotient, retaining the exceptional
whole-action alternative and the genuinely unresolved recognition branches. -/
theorem strict_corrected_conclusion_or_remaining
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
    ChapterG.Section11.FullLinearFour.ConclusionWithFullLinearFour
      (strictRepresentation T L R z) B v
      (strictHatSpace T L R z (strictCrossingIntersection T L R z d))
      (strictCrossingImage T L R z d)
      ((strictCrossingCenterImage T L R z d).subgroupOf (strictCrossingImage T L R z d)) ∨
      (IsIrreducible (strictRepresentation T L R z) ∧
        6 ≤ finrank (ZMod 2) (Additive (StrictVectorQuotient T L R z)) ∧
        ((Group.IsSolvable (StrictActor T L R z) ∧
            finrank (ZMod 2) (Additive (strictCrossingImage T L R z d)) = 2 ∧
            finrank (ZMod 2) (Additive (StrictVectorQuotient T L R z)) = 6) ∨
          (¬ Group.IsSolvable (StrictActor T L R z) ∧
            ChapterG.Section11.ExchangedRecognition.RemainingComponentModels (strictRepresentation T L R z) B v
              (strictHatSpace T L R z (strictCrossingIntersection T L R z d))
              (strictCrossingImage T L R z d)))) :=
  ChapterG.Section11.ExchangedRecognition.corrected_conclusion_or_remaining h cover ⟨a,ha,hr,hv⟩ ⟨S,hSv,hXS,hXn⟩


end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
