module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.CriticalProfileCentral
public import Theory.GroupTheory.WeakBNPair.RegularTree.RadiusThreeCover

/-!
# Radius-three fixation by the central middle subgroup

For an original noncommuting critical pair at distance two, the middle
subgroup Z is central in its local actor. The common edge Sylows put it in
the center subgroup of every neighbor. Each neighboring center fixes its
radius-two ball by the global critical-distance minimum. These balls cover
the middle vertex's radius-three ball.

This supplies the radius-three input for the binary reflection correction
on the original universal six-path, after lifting through the coset covering.
Source: DGS, Groups and Graphs (1985), (3.8), (10.6), and (14.17),
printed pp.81--83, 157--158 and 223.
-/

public section
open Subgroup Theory.GroupTheory.WeakBNPair.RegularTree
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open NoncommutingProfile
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S

/-- The central middle subgroup of the original noncommuting critical pair
fixes the whole radius-three ball, with no ball-fixation premise. -/
theorem reduced_bTwo_middle_radius_three
    (h : HypothesisF11 L S)
    {v m w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : b F = 2) (hvm : (graph F).Adj v m) (hmw : (graph F).Adj m w) :
    Z F m ≤ graphBallFixer (graph F) m 3 := by
  have hcentral := reduced_bTwo_middle_central h hc hne hb hvm hmw
  have hgen : F false ⊔ F true = ⊤ := (reduced_triple h).generate
  intro z hz
  apply graphBallFixer_radius_three_of_neighbor (graph F) m z
  · exact Z_le_stabilizer F m hz
  · intro u hum
    have hzu : Z F m ≤ Z F u := center_le_of_central_neighbor
      (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h)
      hum.symm hcentral
    rw [mem_graphBallFixer]
    intro x hx
    have hdist : (graph F).dist u x ≤ 2 := (mem_ball_iff F hgen u x 2).mp hx
    exact Z_le_stabilizer_of_dist_le_b F hgen u x (by rwa [hb]) (hzu hz)

end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
