module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationMSPair
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Recognition.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.Application
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Assembly.Complete.Source
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.A6Irreducibility

/-!
# The original augmentation Baumann/short-block alternative

Let R = O₂(L₁T) for either escaping nonconstant weight in the original
five-dimensional augmentation module. The small Baumann images already give
normalizer containment or shortness. In the full-image branch, failure of
normalizer containment gives the literal MS pair on L Baum(R), with every
local MS condition proved. Ordinary A₆ is centerless, so the proved initial
recognition and distance-two exhaustion leave only the independent natural
large-distance input. Reconstruction then proves shortness of the whole L.

Thus the conclusion is the actual alternative used in 13.2.2(7), with
no chosen four-dimensional submodule, shortness or MS-pair assumption.
This theorem is conditional on the existing natural large-distance input,
owned by qt-e-ms-small-a6-exhaustion-large-distance. Its discharge and the
remaining 13.4.10–17 arguments remain with qt-d-1341-nonsolvable-source.
AugmentationDoubledExclusion is the actual doubled-row consumer. Both
nonconstant weights and the original central quotient projection are retained.

Source: Aschbacher–Smith C.1.31–32, pp.135–136; C.1.37, pp.142–143;
13.2.2(7), pp.877–878, and 13.4.10(4), p.909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The full ordinary augmentation alternative, pending only the independent
natural large-distance theorem. It applies at either nonconstant weight. -/
theorem ordinary_augmentation_baumann_alternative_of_largeDistance
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
    normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G) ∨ ChapterC.IsShort L := by
  let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
  let B := ChapterB.baumann R
  by_cases hbound : normalizer (B : Set G) ≤ normalizer (L : Set G)
  · exact Or.inl hbound
  obtain ⟨q,hq,_,_,_⟩ := exists_core_product_permutation D m h structural eL
  rcases ordinary_augmentation_baumann_images h structural D m eL z hzT hzL q hq with hs | hf
  · exact ordinary_augmentation_small_baumann h structural D m eL z hzT hzL q hq hs
  have hcond := ordinary_augmentation_full_ms_conditions h structural D m eL z hzT hzL q hq hf hbound
  have hms : SmallMSPair KnownSimple.IsKnownSimple L B :=
    ordinary_augmentation_smallMSPair_of_ms_conditions h structural D m eL z hzT hzL hcond
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hh : eL x ∈ center (alternatingGroup (Fin 6)) := (centerCongr eL ⟨x,hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp)] at hh
    exact eL.map_eq_one_iff.mp hh
  let eA : (L ⧸ centralPreimage (pCore 2 L)) ≃*
      commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) := m.quotient.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp)).symm
  have hn := naturalCore_of_distance_inputs initialRecognition_knownSimple hl
    DistanceTwo.distanceTwo_knownSimple
  obtain ⟨hel,hcent,hmodel⟩ := hn G L B hms eA hz
  exact Or.inr (hms.short_of_core hel hcent h.quasisimple hmodel.alternating_six_irreducible)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
