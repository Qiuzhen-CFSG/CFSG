module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.PlaneMS
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Recognition.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.Application
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Assembly.Complete.Source
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.A6Irreducibility

/-!
# Residual movement in the selected ordinary linear plane case

The original linear join normalizes Baum(T) and escapes N_G(L), ruling
out the characteristic-normal alternative and forcing J(T) outside the
LT two-core. If J1(T) stays in the actual plane radical, PlaneMS supplies
the complete MS pair on L Baum(T). The ordinary A6 reconstruction forces
shortness, and the checked short-block exclusion then gives the required
full two-residual commutator equality. The full linear overgroup formula
follows with no supplied shortness or near-maximum containment premise.

The independent Natural.Exhaustion.LargeDistanceInput remains explicit;
its producer is qt-e-ms-small-a6-exhaustion-large-distance. The selected
linear component, ordinary A6 marking and genuine earlier source inputs
are retained. Model selection, the other rows and both universal13.4.7
interfaces remain obligations of the fixed-core source assembly.
Source: Aschbacher--Smith13.2.2(10), p.878;13.4.7(2),(4), pp.902--903.
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
theorem original_plane_short_of_largeDistance
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
  have hms := original_plane_smallMSPair h structural D m eL W hW hTW hB eB hJ hne hescape
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

open Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
variable (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL)
include h₀ D m h1332 hTA hTB eA eB hne hindexA hindexB hK hres eK

/-- In the selected ordinary linear plane case, all pushing-up premises
are constructed and shortness is discharged. The two-residual is moved by
J₁(T), so the full overgroup conclusion follows. Natural large-distance
exhaustion remains the independent earlier source input. -/
theorem original_pair_linear_plane_conclusion_of_largeDistance
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)) :
    ⁅(pResidual 2 B).map B.subtype,ChapterB.thompsonJ (T : Subgroup G) 1⁆ =
        (pResidual 2 B).map B.subtype ∧
      Solvable.LinearAmalgamConclusion T (A ⊔ B) ∧
      ¬ A ⊔ B ≤ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) := by
  have hc : ⁅(pResidual 2 B).map B.subtype,ChapterB.thompsonJ (T : Subgroup G) 1⁆ =
      (pResidual 2 B).map B.subtype := by
    apply (original_residual_thompson_one_iff hTB eB).mpr
    intro hJ
    obtain ⟨_,hbN,_,hJne⟩ := original_pair_linear_baumann_obstructions h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK hres eK h structural hout hindexL
    have hescape : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
        normalizer (L : Set G) := fun hb => hout (hbN.trans hb)
    have hb := original_plane_short_of_largeDistance hl h structural D m eL W hW hTW hB
      eB hJ hJne hescape
    have hshort := original_pair_linear_short_conclusion h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK hres eK h structural hout hindexL hb W hW hTW hB
    exact ((original_residual_thompson_one_iff hTB eB).mp hshort.1) hJ
  exact ⟨hc,original_pair_linear_amalgam_conclusion h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK hres eK h structural hout hindexL hc,
    not_thompson_one_normalizer_of_residual_movement hTB eB le_sup_right hc⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
