module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.Inputs
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore.Exclusion
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.EightExclusion
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ElementaryCubeClosure
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.PointExclusion
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure.SecondFailure

/-!
# The remaining unequal image-sixteen case at critical distance four

The completed mixed, cube, full point, and nonelementary image-eight
exclusions leave radical image order sixteen. The original radical is Sylow,
its restriction has index one over the replacement radical, and the literal
initial critical path supplies the two unequal source selections. Their
second order-two line lies in the old edge seed and centralizes the new
residual, but fails to centralize the first selected mover.

This theorem exposes the remaining source obstruction. It does not assert
that the first selected mover fixes this line or exclude distance four.
Both full moved covers and all central attachments are retained.

Source: MS93 (5.12), printed pp.924--927, especially the second source line
on printed p.925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.RemainingSixteen
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
local notation "edgeMover" => fun a t : Vertex d.radical =>
  SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4

include e hz hn in
private theorem original_sylow_knownSimple
    (hb : replacementDistance h d = 4) :
    ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R) := by
  by_contra hns
  rcases nonsylow_radical_image_maximal_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hns with
      ⟨u,hu⟩ | ⟨u,hu⟩
  · exact full_point_distance_four_false_knownSimple hb u hu
  · exact cube_distance_four_false_knownSimple hb u hu

private theorem four_image_false_knownSimple
    (hb : replacementDistance h d = 4)
    (hfour : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 4) : False := by
  obtain ⟨u,hu⟩ := PairExclusion.four_image_mixed_knownSimple (by omega) hfour
  exact MixedWholeCore.distance_four_false_knownSimple hb u hu

private theorem image_nonelementary_knownSimple
    (hb : replacementDistance h d = 4) :
    ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)) := by
  intro hel
  obtain ⟨T,hT⟩ := original_sylow_knownSimple (e := e) (hz := hz) (hn := hn) hb
  let A := d.radical.map (SourceReduction.projection h e hz hn d)
  by_cases hfour : Nat.card A = 4
  · exact four_image_false_knownSimple hb hfour
  have hlarge : 8 ≤ Nat.card A := by
    obtain ⟨_,_,hprod,hidx⟩ := SylowRestriction.original_sylow_restriction_knownSimple
      (e := e) (hz := hz) (hn := hn) (d := d) (by omega) T hT
    change Nat.card A * _ = 16 at hprod
    rcases hidx with hi | hi | hi <;> rw [hi] at hprod <;> omega
  have he : Representation.BinaryOffender.IsElementaryTwo A := ⟨by
    intro hz
    rw [hz,card_bot] at hlarge
    omega,hel⟩
  obtain ⟨C,hC,hCD | hCE,hAC⟩ := exists_conjugate_le_D_or_exceptional he
  · have hDcard : Nat.card (D 6) = 8 := card_disjointTranspositions (3 : Fin 4)
    have hCfull : C = D 6 := eq_of_le_of_card_ge hCD (by
      rw [hDcard,←hAC.card_eq]
      exact hlarge)
    obtain ⟨u,hu⟩ := hAC
    apply cube_distance_four_false_knownSimple hb u
    exact hu.trans (congrArg (Subgroup.map (MulAut.conj u).toMonoidHom) hCfull)
  · have hCfull : C = exceptional 6 (by decide) := eq_of_le_of_card_ge hCE (by
      rw [card_exceptional,←hAC.card_eq]
      exact hlarge)
    obtain ⟨u,hu⟩ := hAC
    apply full_point_distance_four_false_knownSimple hb u
    change A = _
    rw [hu,hCfull,CFSG.Quasithin.ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional]

/-- Every actual critical-distance-four replacement has radical image order
sixteen, after the completed smaller-image branches are discharged. -/
theorem image_sixteen_knownSimple
    (hb : replacementDistance h d = 4) :
    Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16 := by
  obtain ⟨T,hT⟩ := original_sylow_knownSimple (e := e) (hz := hz) (hn := hn) hb
  obtain ⟨_,_,hprod,hidx⟩ := SylowRestriction.original_sylow_restriction_knownSimple
    (e := e) (hz := hz) (hn := hn) (d := d) (by omega) T hT
  rcases hidx with hi | hi | hi
  · simpa only [hi,Nat.mul_one] using hprod
  · have hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8 := by
      rw [hi] at hprod
      omega
    exact (eight_distance_four_false_knownSimple (image_nonelementary_knownSimple hb) hcard hb).elim
  · have hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 4 := by
      rw [hi] at hprod
      omega
    exact (four_image_false_knownSimple hb hcard).elim

/-- The remaining source branch retains the original Sylow radical, its
exact restriction index, and nonelementarity in the literal projection. -/
theorem original_radical_configuration_knownSimple
    (hb : replacementDistance h d = 4) :
    (∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R)) ∧
      (¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d))) ∧
      d.radical.relIndex ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup) = 1 ∧
      Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16 := by
  obtain ⟨T,hT⟩ := original_sylow_knownSimple (e := e) (hz := hz) (hn := hn) hb
  have hcard := image_sixteen_knownSimple (e := e) (hz := hz) (hn := hn) hb
  obtain ⟨_,_,hprod,_⟩ := SylowRestriction.original_sylow_restriction_knownSimple
    (e := e) (hz := hz) (hn := hn) (d := d) (by omega) T hT
  refine ⟨⟨T,hT⟩,image_nonelementary_knownSimple hb,?_,hcard⟩
  rw [hcard] at hprod
  omega

include e hz hn in
/-- Critical distance four alone supplies the literal unequal two-step
source configuration and its unfixed second order-two line. No additional
image, strict-slice, path-selection, or fixation premise is assumed. -/
theorem selected_second_source_line_knownSimple
    (hb : replacementDistance h d = 4) :
    ∃ z, ∃ p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) ∧
      ∃ c b : Vertex d.radical,
        ∃ q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2),
        ∃ r : CriticalPath d.radical (replacementGeometry h d) b (alpha d.radical),
          q.walk.getVert 2 = alpha d.radical ∧ r.walk.getVert 2 = c ∧
          (∃ g ∈ stabilizer d.radical (alpha d.radical),
            act d.radical g (p.walk.getVert 2) = c ∧
            act d.radical g (p.walk.getVert 1) = q.walk.getVert 1) ∧
          (∃ j ∈ stabilizer d.radical (q.walk.getVert 1),
            act d.radical j (alpha d.radical) = c ∧
            ∃ k ∈ stabilizer d.radical c,
              act d.radical k (act d.radical j c) = b ∧
              act d.radical k (q.walk.getVert 1) = r.walk.getVert 1) ∧
          edgeMover c (q.walk.getVert 1) ≠ edgeMover (alpha d.radical) (q.walk.getVert 1) ∧
          edgeMover (alpha d.radical) (p.walk.getVert 1) ⊔
            edgeMover (alpha d.radical) (q.walk.getVert 1) = stabilizer d.radical (alpha d.radical) ∧
          Q d.radical (q.walk.getVert 1) ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
          2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
            (U d.radical c) ∧
          edgeMover b (r.walk.getVert 1) ≠ edgeMover c (r.walk.getVert 1) ∧
          Q d.radical (r.walk.getVert 1) ⊔ Z d.radical (p.walk.getVert 2) = stabilizer d.radical c ∧
          2 < (B d.radical c ((replacementGeometry h d).Z_normal _)).relIndex
            (U d.radical b) ∧
          let H := ⁅U d.radical b ⊓ Q d.radical (alpha d.radical),
            X d.radical (p.walk.getVert 2) ⊓ Q d.radical c⁆
          Nat.card (H : Subgroup (FreeAmalgam d.radical)) = 2 ∧
            H ≤ Z d.radical (p.walk.getVert 1) ∧
            H ≤ centralizer (Ltilde d.radical c : Set (FreeAmalgam d.radical)) ∧
            ¬ H ≤ centralizer
              (edgeMover (alpha d.radical) (q.walk.getVert 1) : Set (FreeAmalgam d.radical)) := by
  obtain ⟨z,p,hnon,hstrict⟩ := EightInitialSelection.initial_selection_all_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  exact ⟨z,p,hnon,hstrict,SixteenClosure.selected_second_source_line_knownSimple
    (image_sixteen_knownSimple (e := e) (hz := hz) (hn := hn) hb) hb p hstrict⟩

/-- The original distance-four input now requires only the image-sixteen
exclusion. This conditional adapter passes the given symmetric action and
central layer unchanged, and proves its image-order premise internally. -/
theorem distanceFourInput_of_sixteen
    (hsixteen : ∀ (G : Type u) [Group G] [Finite G] (L R : Subgroup G)
      (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
      (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
      (d : Replacement L R) (s : FullSymmetricAction h e hz hn d),
      DistanceTwo.CentralLayer d → replacementDistance h d = 4 →
        Nat.card (d.radical.map s.projection) = 16 → False) :
    DistanceFourInput.{u} KnownSimple.IsKnownSimple := by
  intro G _ _ L R h e hz hn d s hc hb
  have hcard : Nat.card (d.radical.map s.projection) = 16 := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
    exact image_sixteen_knownSimple (e := e) (hz := hz) (hn := hn) hb
  exact hsixteen G L R h e hz hn d s hc hb hcard

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.RemainingSixteen
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
