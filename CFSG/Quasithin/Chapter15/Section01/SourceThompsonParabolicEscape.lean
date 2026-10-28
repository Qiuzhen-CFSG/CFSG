module

public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonPrepared
public import Theory.GroupTheory.PResidual.MinimalParabolicEscape

/-!
# The precise parabolic selection from the Thompson fixed-space escape

For the original chosen V, failure of15.1.14(1) selects a characteristic-two
minimal parabolic P inside C_G(Z) whose residual moves C_V(J₁(T)). Selection
is minimal outside the join appearing in the displayed escape inequality.
The already proved15.1.12(4) implies that P is not an H-star member; hence P
contains a strictly smaller H-star member inside that join. This records the
exact remaining distinction between the elementary selection and the H-star
selection asserted in the source. It does not establish15.1.14(1).

Source: Aschbacher--Smith,15.1.14(1), printed p.1091.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem PreparedChosenModule.thompsonFixed_moving_minimalParabolic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V)
    (hnot : ¬ (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    let C := centralizer (centralInvolutions T : Set G)
    let K := (M ⊓ C) ⊔ ((pResidual 2 C).map C.subtype ⊓
      centralizer (thompsonFixed T V : Set G))
    ∃ P : Subgroup G, P ≤ C ∧ P ∈ Chapter1.HOver G (T : Set G) ∧
      ChapterB.IsMinimalParabolicOver T P ∧ IsSQTK KnownSimple.IsKnownSimple P ∧
      generalizedFitting P = pCore 2 P ∧ ¬ P ≤ M ∧
      ¬ (pResidual 2 P).map P.subtype ≤ centralizer (thompsonFixed T V : Set G) ∧
      ∀ Y : Subgroup G, (T : Subgroup G) ≤ Y → Y < P → Y ≤ K := by
  have hTC : (T : Subgroup G) ≤ centralizer (centralInvolutions T : Set G) := by
    intro t ht z hz
    exact (((mem_omegaOneCenterAmbient_iff _ z).mp hz).2.2 t ht).symm
  have hNT : normalizer (T : Set G) ≤ M :=
    (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.2
  obtain ⟨P,hPC,hP,hPM,hres,hproper⟩ := exists_minimalParabolic_of_residual_escape T
    (centralizer (centralInvolutions T : Set G)) M (thompsonFixed T V)
    hTC hM.1.2 (inf_le_right.trans hNT) (h.thompsonFixed_residual_escape T hM hnot)
  have hTP : (T : Subgroup G) ≤ P := hP.1.1.le
  have hZT : centralInvolutions T ≤ (T : Subgroup G) := by
    intro z hz
    exact ((mem_omegaOneCenterAmbient_iff _ z).mp hz).1
  have hZcore : centralInvolutions T ≤ P.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (T.isPGroup'.to_le hZT) (hZT.trans hTP)
      (hPC.trans (Subgroup.centralizer_le_normalizer _))
  have hPH : P ∈ Chapter1.HOver G (T : Set G) := by
    refine ⟨?_,hTP⟩
    intro he
    exact centralInvolutions_ne_bot_of_maximal_local T hM.1 (bot_unique (he ▸ hZcore))
  refine ⟨P,hPC,hPH,hP,Chapter3.sqtk_of_mem_H hG hPH.1,?_,hPM,hres,hproper⟩
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2
    (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hPH))

theorem PreparedChosenModule.thompsonFixed_moving_parabolic_nested
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V)
    (hnot : ¬ (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    let C := centralizer (centralInvolutions T : Set G)
    let K := (M ⊓ C) ⊔ ((pResidual 2 C).map C.subtype ⊓
      centralizer (thompsonFixed T V : Set G))
    ∃ P H : Subgroup G, P ≤ C ∧ ChapterB.IsMinimalParabolicOver T P ∧
      P ∉ Chapter3.HStar (T : Subgroup G) M ∧
      H ∈ Chapter3.HStar (T : Subgroup G) M ∧ H < P ∧ H ≤ K ∧
      ¬ (pResidual 2 P).map P.subtype ≤ centralizer (thompsonFixed T V : Set G) ∧
      (pResidual 2 H).map H.subtype ≤ centralizer (thompsonFixed T V : Set G) := by
  classical
  obtain ⟨P,hPC,hPH,hP,_,_,hPM,hres,hproper⟩ :=
    h.thompsonFixed_moving_minimalParabolic hG T hM hJ hnot
  have hlocal := h.source_thompsonFixed_local_residuals hG T hempty hM hJ
  have hnotStar : P ∉ Chapter3.HStar (T : Subgroup G) M := fun hs => hres (hlocal P hs)
  let S : Set (Subgroup G) :=
    {Y | Y ∈ Chapter1.HOver G (T : Set G) ∧ ¬ Y ≤ M ∧ Y ≤ P}
  obtain ⟨H,hH⟩ := (Set.toFinite S).exists_minimalFor id S ⟨P,hPH,hPM,le_rfl⟩
  have hHS : H ∈ Chapter3.HStar (T : Subgroup G) M := by
    refine ⟨⟨hH.1.1,hH.1.2.1⟩,?_⟩
    intro Y hY hYH
    exact hH.2 ⟨hY.1,hY.2,hYH.trans hH.1.2.2⟩ hYH
  have hHP : H < P := lt_of_le_of_ne hH.1.2.2 (fun he => hnotStar (he ▸ hHS))
  exact ⟨P,H,hPC,hP,hnotStar,hHS,hHP,hproper H hH.1.1.2 hHP,hres,hlocal H hHS⟩

end CFSG.Quasithin.Chapter15.Section01
