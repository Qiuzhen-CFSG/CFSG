module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.CubicPlacement
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.SmallStar
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.RankOne

/-!
# Closing the original A₅ star branch

The rank intersection construction supplies the marked cubic in the actual
component. Characteristic two on JQ and the original Sylow placement then
put the perpendicular sixteen-group inside the literal U(J), where the
L₂(4) natural-block bound gives a contradiction. Applying the full-Sylow
A₅ star reduction discharges that entire catalogue branch.

The remaining reduction retains the original moved section in the two
odd-degree linear-three rows and a genuine natural rank-one block with
field parameter still to be bounded. These remaining field and chief-factor
arguments belong to this plane-centralizer assembly.
Source: Aschbacher--Smith 13.3.12, printed pp.889--890.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
open Representation Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

/-- The actual join has characteristic two, and the component now supplies
the exact cubic required by the terminal rank-one row. -/
theorem Context.rankOneRow_of_four_block (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J)
    (hs : Chapter1.IsSylowIn 2 ((L ⊔ T).pCoreIn 2) (J ⊔ (L ⊔ T).pCoreIn 2))
    (hb : ChapterC.IsL2EvenBlock J 2) : RankOneRow T L d J := by
  refine ⟨hb,hs,?_,s.component_marked_cubic d J j⟩
  have hc := ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
    (G := (J ⊔ (L ⊔ T).pCoreIn 2 : Subgroup G))
  rwa [ChapterC.C27Source.source_join_fitting j.input] at hc

/-- The original perpendicular sixteen-group excludes every actual L₂(4)
block with the selected radical Sylow in the join. -/
theorem Context.not_four_block (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J)
    (hs : Chapter1.IsSylowIn 2 ((L ⊔ T).pCoreIn 2) (J ⊔ (L ⊔ T).pCoreIn 2))
    (hb : ChapterC.IsL2EvenBlock J 2) : False := by
  have r := s.rankOneRow_of_four_block d J j hs hb
  obtain ⟨n,hnJ,hn⟩ := r.cubic
  exact not_rankOne_of_source_join d.chart d.coordinates d.equivariant n hn
    J ((L ⊔ T).pCoreIn 2) r.block hnJ j.input.normalizes r.sylow
    r.characteristic (chosen_perpendicular_central s d.coordinates)

/-- The literal A₅ star image is excluded after full Sylow placement and
the genuine perpendicular-space contradiction on its original component. -/
theorem Context.not_alternatingFive_star (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J)
    (e : starImage J ((L ⊔ T).pCoreIn 2) J ≃* alternatingGroup (Fin 5)) : False := by
  obtain ⟨hs,hb⟩ := s.four_block_of_alternatingFive_star d J j e
  exact s.not_four_block d J j hs hb

/-- Outside the odd-degree linear-three rows the original natural block
has a parameter different from two. This is a reduction, not the full
field bound needed by 13.3.12. -/
theorem Context.remaining_block_or_odd_linearThree (s : Context T L V)
    (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J) :
    let ρ := starRepresentation J ((L ⊔ T).pCoreIn 2)
    let B := offenderSubgroup ρ
    let K := (starImage J ((L ⊔ T).pCoreIn 2) J).subgroupOf B
    (Chapter1.IsSylowIn 2 ((L ⊔ T).pCoreIn 2) (J ⊔ (L ⊔ T).pCoreIn 2) ∧
      ∃ n, n ≠ 2 ∧ ChapterC.IsL2EvenBlock J n) ∨
    ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp B.subtype) K, PlaneOddLinearThreeCase (ρ.comp B.subtype) K c.sectionData := by
  rcases s.even_block_or_odd_linearThree d J j with ⟨hs,n,hb⟩ | h
  · exact Or.inl ⟨hs,n,fun hn => s.not_four_block d J j hs (hn ▸ hb),hb⟩
  · exact Or.inr h

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
