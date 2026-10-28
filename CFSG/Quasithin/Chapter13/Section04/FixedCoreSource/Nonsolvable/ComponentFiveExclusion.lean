module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFiveBlock
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.BlockContainment
public import Stellmacher.MaxElementaryOffenderEquality
public import Stellmacher.ElementaryAbelianMaxJFixedCenter

/-!
# Excluding the selected A₅ component in the ordinary augmentation row

The two-chief-factor budget recognizes the selected component K as an A₅
block. Every maximal elementary subgroup A of O₂(LT) is maximal in the
original point radical O₂(L₁T), since their two-ranks agree. The Thompson
comparison puts A in O₂(KT); hence A centralizes and contains the elementary
block layer U. Shortness gives [A,K] ≤ U ≤ A. Thus K normalizes J(O₂(LT)),
whose normalizer lies in N_G(L) by the original maximal-local uniqueness.
This contradicts the selected component's escape from N_G(L).

The proof uses the actual original point residual and both possible nonconstant
weights in the five-dimensional augmentation module. The independent natural
large-distance input remains explicit, with producer
qt-e-ms-small-a6-exhaustion-large-distance. The covered original row, other
module rows, reciprocal comparison, commutator and graph assembly remain with
qt-d-1341-nonsolvable-source. Universal nonsolvability at both escaping weights
is still required for that assembly; no full source theorem is asserted here.
Source: Aschbacher–Smith 13.4.10(1), printed p.908.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

/-- The ordinary original A₆ row cannot have an escaping selected A₅ component. -/
theorem ordinary_five_excluded_of_largeDistance
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) : False := by
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  let X := K ⊔ (T : Subgroup G)
  let QK := X.pCoreIn 2
  let Y := L ⊔ (T : Subgroup G)
  let QL := Y.pCoreIn 2
  let P := Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)
  let R := P.pCoreIn 2
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  obtain ⟨hb,_⟩ := ordinary_five_block_of_largeDistance hl h₀ h structural D m h1332 modules
    eL z hzT hzL hKz hHN hKM hfK eK
  obtain ⟨DK,_,_,_⟩ := component_five_marking h₀ h structural D m h1332 modules
    hzT hz1 hKz hHN hKM hfK eK
  let := DK.elementary
  have hJ : elementaryAbelianMaxJ R = elementaryAbelianMaxJ QK :=
    (ordinary_five_original_baumann h₀ h structural D m h1332 modules
      eL z hzT hzL hKz hHN hKM hfK eK).1
  have hr : ChapterB.twoRank R = ChapterB.twoRank QL :=
    (ordinary_augmentation_point_rank h structural D m eL z hzT hzL).1
  have hPY : P ≤ Y := sup_le
    ((Solvable.firstCentralizerResidual_le L z.val).trans inf_le_left |>.trans le_sup_left)
    le_sup_right
  have hQP : QL ≤ P := by
    dsimp only [P]
    rw [ordinary_augmentation_point_parabolic D m eL z hzT hzL]
    exact le_inf (pCoreIn_le 2 Y)
      (D.core_centralizes.trans (centralizer_le (Set.singleton_subset_iff.mpr z.property)))
  have hQR : QL ≤ R := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 Y) hQP
    (hPY.trans (Y.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))))
  obtain ⟨_,_,w,_,_,hP⟩ := ordinary_five_component_residuals h₀ h structural D m h1332 modules
    eL z hzT hzL hKz hHN hKM hfK eK
  have hPX : P ≤ X := hP.le.trans inf_le_left
  have hKP : QK ≤ P := by
    dsimp only [P]
    rw [hP]
    exact le_inf (pCoreIn_le 2 X)
      (DK.core_centralizes.trans (centralizer_le (Set.singleton_subset_iff.mpr w.property)))
  have hKR : QK ≤ R := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 X) hKP
    (hPX.trans (X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))))
  have hUR : U ≤ R := DK.le_core.trans hKR
  have hKT : QK ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ X from le_sup_right)] using
      pCoreIn_le_sylow X (T.subtype le_sup_right)
  have hJK : elementaryAbelianMaxJ QK ≤ QK := sSup_le fun _ hA => hA.1
  have hnormal (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups QL) :
      K ≤ normalizer (A : Set G) := by
    have hAR : A ∈ elementaryAbelianMaxSubgroups R := by
      refine ⟨hA.1.trans hQR,hA.2.1,?_⟩
      intro B hBR hB
      have hcard : Nat.card A = elementaryAbelianMaxOrder R := by
        rw [card_eq_elementaryAbelianMaxOrder QL A hA,
          ChapterB.maxOrder_eq_two_pow_rank,ChapterB.maxOrder_eq_two_pow_rank,hr]
      rw [hcard]
      obtain ⟨B₀,hB₀⟩ := elementaryAbelianMaxSubgroups_nonempty R
      exact (hB₀.2.2 B hBR hB).trans_eq (card_eq_elementaryAbelianMaxOrder R B₀ hB₀)
    have hAK : A ≤ QK := (le_sSup hAR).trans (hJ.le.trans hJK)
    have hUA : U ≤ A := maxElementary_contains_elementary_centralizer R A U hAR hUR
      (le_centralizer_iff.mp (hAK.trans DK.core_centralizes))
    apply le_normalizer_iff_commutator_le_left.mpr
    exact (commutator_mono (le_inf (hAK.trans hKT) (hAK.trans DK.core_centralizes)) le_rfl).trans
      ((Solvable.sylow_module_centralizer_commutator_le_chosen DK hb.2.1).trans hUA)
  have hKJ : K ≤ normalizer (elementaryAbelianMaxJ QL : Set G) := by
    change K ≤ normalizer ((sSup (elementaryAbelianMaxSubgroups QL) : Subgroup G) : Set G)
    rw [sSup_eq_iSup']
    exact (le_iInf fun A : elementaryAbelianMaxSubgroups QL => hnormal A A.property).trans
      (iInf_normalizer_le_normalizer_iSup _)
  have hJQ : elementaryAbelianMaxJ QL ≤ QL := sSup_le fun _ hA => hA.1
  have hYN : Y ≤ normalizer (elementaryAbelianMaxJ QL : Set G) :=
    (Y.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))).trans
      (normalizer_le_normalizer_elementaryAbelianMaxJ QL)
  let := D.elementary
  have hVJ : V ≤ elementaryAbelianMaxJ QL := by
    have hv := elementary_centralizer_maxJ_le_omegaCenter QL V D.le_core
      ((le_centralizer_iff.mp D.core_centralizes).trans (centralizer_le hJQ))
    intro v hvV
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp (hv hvV)).1
  have hne : elementaryAbelianMaxJ QL ≠ ⊥ := fun hh => D.ne_bot (eq_bot_iff.mpr (hh ▸ hVJ))
  have hbound := normalizer_le_of_unique_maximalTwoLocal
    (h.source_normalizer_maximal_unique structural
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2
    ((isPGroup_pCoreIn 2 Y).to_le hJQ) hne hYN
  exact hKM (hKJ.trans hbound)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
