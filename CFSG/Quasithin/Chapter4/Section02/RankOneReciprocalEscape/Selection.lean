module
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Configurations
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Alignment

/-!
# Selecting the full normalized ambient witnesses

The original odd fixed residual supplies a maximal pushing-up counterexample,
its full module and its inclusion-induced core quotient equivalence. Sylow
conjugacy in the literal section centralizer aligns its two-core with the
conjugate of O₂(LT). The conjugator is retained together with the original T,
the full-module formula and both conjugate-span equalities of 4.2.3.

Source: Aschbacher--Smith, 4.2.3--4 and 4.2.12, pp.608--610.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
open Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
variable {G : Type*} [Group G] [Finite G]

/-- Every source 4.2.3 clause on the selected counterexample, with the original
Sylow and the actual section-centralizer conjugator retained. -/
theorem aligned_witness_of_not_unique {T : Sylow 2 G} {L V : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)))
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ∃ J H W : Subgroup G, Witness L V A J H W ∧
      ∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
        let T' : Sylow 2 G := (c : G) • T
        let Mminus := coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)
        Mminus ∈ sigma (normalizer (L : Set G)) L ∧
        conjugateSpanBy L (T' : Subgroup G) = L ∧
        conjugateSpanBy L Mminus = L ∧
        J.pCoreIn 2 ≤ (L ⊔ (T' : Subgroup G)).pCoreIn 2 ∧
        (L ⊔ (T' : Subgroup G)).pCoreIn 2 = sectionCentralizerIn (T' : Subgroup G) L ∧
        (L ⊔ (T' : Subgroup G)).pCoreIn 2 =
          ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom ∧
        W = Unitary.fullModule L ((L ⊔ (T' : Subgroup G)).pCoreIn 2) := by
  obtain ⟨hc,_,hVF,hne⟩ := chosen_oddActorResidual_cover h D A hAN hcomm hodd hAV
  have hFL : oddActorResidual L A ≤ L := (oddActorResidual_le L A).trans inf_le_left
  have hFN := hFL.trans L.le_normalizer
  obtain ⟨hsigma,_⟩ := coveringOvergroup_eta L.le_normalizer le_rfl hFN hc.subset hne
  obtain ⟨J,H,S,hJ,hpush,hH,hJH,_,hstrict,hRS,hC,c,hmark,hVW⟩ :=
    Unitary.exists_source_C28_of_not_unique h D hM hFN hc.subset hne hnot
  have hVJ : V ≤ J.pCoreIn 2 := hVF.trans hpush.1
  have hr := chosen_intersection_twoResidual_eq_solvableResidual h hJ.1.1.2.2.1 hJH
  have hd := chosen_oddActorResidual_counterexample_residual h D hJ.1.1.2.2.1 hJH hVJ
  rw [hr] at hd
  obtain ⟨e,he⟩ := exists_pCoreQuotientEquiv_of_cover
    ((map_subtype_le _).trans inf_le_left) hd.1.subset
  have hsize := card_le_of_le hVW
  rw [card_map_of_injective (MulAut.conj (c : G)).injective] at hsize
  refine ⟨J,H,_,⟨hJ,hpush,hH,hJH,hstrict,hVJ,hC,hd.1,hd.2.2.1,hd.2.2.2.1,
    hd.2.2.2.2,⟨e,he⟩,hC.oddCore_eq_bot,hC.isRadical,hC.sylow_in_normalClosure,
    hC.section_fitting_eq_core,hC.section_sylow_in_H,hsize,c,hVW⟩,c,?_⟩
  have halign := aligned_sylow_core (source_hypothesis411 h hM).plus_perfect
    D.sylow_normalizes_component c
  have hL : L.map (MulAut.conj (c : G)).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp c.property.1
  have hTc : (((c : G) • T : Sylow 2 G) : Subgroup G) ≤ normalizer (L : Set G) := by
    change (T : Subgroup G).map (MulAut.conj (c : G)).toMonoidHom ≤ _
    exact (map_mono D.sylow_normalizes_component).trans (by rw [map_equiv_normalizer_eq,hL])
  refine ⟨hsigma,le_antisymm (conjugateSpanBy_le le_rfl hTc) (le_conjugateSpanBy _ _),
    le_antisymm (conjugateSpanBy_le le_rfl hsigma.1) (le_conjugateSpanBy _ _),
    ?_,halign.2,halign.1,?_⟩
  · rwa [halign.1,hmark]
  · rw [halign.1,hmark]
end CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
