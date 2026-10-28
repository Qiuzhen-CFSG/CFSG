module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.SourceApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.EarlierInputs

/-!
# The reverse neighbor in the critical geometry

The preceding neighbor supplied by 8.1 lies on the geodesic from the first
neighbor to the critical endpoint.  Together with the original first edge,
the two triangle inequalities identify it as a valid first neighbor for the
oppositely oriented critical distance.  This is only a distance transport;
it does not assert the reverse escape or the reverse 8.3 failure hypothesis.

Source: DGS, *Groups and Graphs* (1985), 8.1 and the reorientation used after
8.2, pp.133--134.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
universe u
variable {G : Type u} [Group G]

/-- The previous neighbor from the critical geometry is at distance `b - 1`
from the original first endpoint.  Hence it is a legitimate first neighbor
when the critical pair is read in the opposite direction. -/
theorem reduced_previous_neighbor_reverse_distance
    {J : Fin 2 → Subgroup G} {S₀ : Subgroup G} (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,
      Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥) :
    ∃ prev : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj a' prev ∧
      (graph (Reduction.reducedFamily J S₀)).dist prev a + 1 =
        b (Reduction.reducedFamily J S₀) ∧
      V (Reduction.reducedFamily J S₀) beta 1 ≤ Q (Reduction.reducedFamily J S₀) prev ∧
      ¬ Q (Reduction.reducedFamily J S₀) prev ≤ Q (Reduction.reducedFamily J S₀) a' := by
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  obtain ⟨_, _, _, _, prev, hp, hdist, hescape, hnot⟩ :=
    reduced_critical_geometry h d hc hab hd hb hcomm
  refine ⟨prev, hp, ?_, hescape, hnot⟩
  have hlow := (connected_graph (Reduction.reduced_triple h)).dist_triangle
    (u := a) (v := prev) (w := a')
  change (graph F).dist a a' ≤ (graph F).dist a prev + (graph F).dist prev a' at hlow
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hp.symm] at hlow
  have hupp := (connected_graph (Reduction.reduced_triple h)).dist_triangle
    (u := a) (v := beta) (w := prev)
  change (graph F).dist a prev ≤ (graph F).dist a beta + (graph F).dist beta prev at hupp
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hab] at hupp
  have hc_dist : (graph F).dist a a' = b F := by
    exact hc.1
  change (graph F).dist beta prev + 1 = (graph F).dist beta a' at hdist
  change (graph F).dist beta a' + 1 = b F at hd
  have hlow' : b F ≤ (graph F).dist a prev + 1 := by
    rw [hc_dist] at hlow
    exact hlow
  have hupp' : (graph F).dist a prev + 1 ≤ b F := by
    omega
  change (graph F).dist prev a + 1 = b F
  rw [SimpleGraph.dist_comm]
  omega

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
