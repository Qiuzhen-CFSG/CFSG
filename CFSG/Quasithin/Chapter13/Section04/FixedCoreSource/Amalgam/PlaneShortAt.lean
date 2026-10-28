module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearPlaneSource
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.PlaneMSAt

/-!
# Shortness from the original guarded plane

Apply natural A6 reconstruction to the actual MS pair on L Baum(T).
The original ordinary quotient and augmentation coordinates identify
the resulting short core. The independent natural large-distance
input remains explicit; no universal structural theorem is assumed.
AlternatingPlaneExclusionAt applies this to the selected amalgam row.
Source: Aschbacher--Smith 13.2.2(10), p.878, and 13.4.7(4), p.903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

open AlternatingSixReconstruction.Natural AlternatingSixReconstruction.Natural.Exhaustion

/-- Failure of near-maximum escape in the actual ordinary plane forces
shortness, with only the independent natural large-distance input retained. -/
theorem original_plane_short_of_largeDistance_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (hJ : ChapterB.thompsonJ (T : Subgroup G) 1 ≤ B.pCoreIn 2)
    (hne : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hescape : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (L : Set G)) : ChapterC.IsShort L := by
  let S := ChapterB.baumann (T : Subgroup G)
  have hms := original_plane_smallMSPair_at h structural D m eL W hW hTW hB eB hJ hne hescape
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
  obtain ⟨hel,hcent,hmodel⟩ := hn G L S hms eA hz
  exact hms.short_of_core hel hcent h.quasisimple hmodel.alternating_six_irreducible

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
