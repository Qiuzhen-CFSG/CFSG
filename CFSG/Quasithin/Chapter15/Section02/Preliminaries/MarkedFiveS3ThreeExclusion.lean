module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.MarkedFiveCriticalAlternatives
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.SmallSolvableS3ThreeCenter

/-!
# The original H-star center excludes the marked-five distance-three branch

The literal marked-five / S₃ pair has second full parabolic H. The
nontrivial original Sylow seed supplies a central involution of H. The DGS
nonzero commuting branch would instead make this same H centerless, after
transport along the actual graph conjugation and original actor inclusion.
Thus this pair has critical distance one. The independent distance-one
exclusion is assembled by the symmetric-three source owner.

This uses the original centrality premise and preserves the D₁₀-to-Sz(2)
enlargement. It does not assert that generic mixed pairs are impossible.
Source: Aschbacher--Smith 15.2.8, printed pp.1109--1110;
DGS, *Groups and Graphs* (1985), 8.1, 8.6 and 12.1.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
open ChapterF.Source ChapterF.Source.DGS85
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] [Finite G]

/-- The marked-five/S₃ pair has critical distance one because its actual
second full parabolic contains the nontrivial central Sylow seed. -/
theorem ChosenSmallSource.marked_five_symmetricThree_distance_one
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))) :
    b (Reduction.reducedFamily ![h.residual ⊔ (M ⊓ Mc).pCoreIn 2,H]
      (T : Subgroup G)) = 1 := by
  obtain ⟨hF,hq,_⟩ := h.marked_five_symmetricThree_recognition_data hd hH he
  have hP := ((h.smallResidualWitness_of_marked_five hd).1.symmetricThree_geometry hH he).2.2.2.1
  apply Assembly.small_solvable_s3_distance_one_of_original_center hF hq he hP
  change center H ≠ ⊥
  intro hz
  obtain ⟨z,hz',ho⟩ := h.HStar_central_involution hH
  rw [hz,mem_bot] at hz'
  rw [hz',orderOf_one] at ho
  omega

end CFSG.Quasithin.Chapter15.Section02
