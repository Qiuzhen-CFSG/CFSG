module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.MarkedFiveCriticalAlternatives
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.SmallSolvableS3DistanceOne

/-!
# Critical distance three for the original marked-five / S₃ pair

The source small-solvable critical alternatives leave distance one or three.
The actual binary endpoint cannot be a commuting distance-one alpha, and
the opposite orientation would force a linear small-solvable alpha.
Hence the original Chapter 15 pair has critical distance three. This
does not exclude the genuine generic Ree/Tits pairs; the remaining source
application must retain Chapter 15's additional marked-module hypotheses.
Source: Aschbacher--Smith 15.2.8, printed pp.1109--1110;
DGS (1985), (11.4)--(11.5), pp.171--172.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
open ChapterF.Source ChapterF.Source.DGS85
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] [Finite G]

/-- The literal marked-five/S₃ source pair has critical distance three;
the critical pair and predecessor are obtained from the actual graph. -/
theorem ChosenSmallSource.marked_five_symmetricThree_distance_three
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))) :
    b (Reduction.reducedFamily ![h.residual ⊔ (M ⊓ Mc).pCoreIn 2,H] (T : Subgroup G)) = 3 := by
  obtain ⟨hF,hq,_⟩ := h.marked_five_symmetricThree_recognition_data hd hH he
  let F := Reduction.reducedFamily ![h.residual ⊔ (M ⊓ Mc).pCoreIn 2,H] (T : Subgroup G)
  let ht := Reduction.reduced_triple hF
  have hpair : ∃ a a' : Vertex F, IsCriticalPair F a a' := source_exists_criticalPair ht
  obtain ⟨a,a',hc⟩ := hpair
  have hne : a' ≠ a := by
    intro heq
    have hp : 0 < b F := source_b_positive ht
    have hdist := hc.1
    rw [heq,SimpleGraph.dist_self] at hdist
    omega
  obtain ⟨beta,hab,hdist⟩ := exists_predecessor F ht.generate a' a hne
  rw [SimpleGraph.dist_comm (u := a') (v := beta),
    SimpleGraph.dist_comm (u := a') (v := a),hc.1] at hdist
  rcases (h.marked_five_symmetricThree_critical_alternatives hd hH he
    a beta a' hc hab hdist).2 with hb | hb
  · exact (Assembly.small_solvable_s3_distance_one_exclusion hF hq he hb).elim
  · exact hb.1

end CFSG.Quasithin.Chapter15.Section02
