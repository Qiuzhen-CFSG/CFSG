module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.CoreReconstruction
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.BlockChiefCount
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.Assembly

/-!
# Original Baumann control from the reduced symplectic source

The literal natural-six source has three alternatives: a nontrivial normal
characteristic subgroup of its Baumann subgroup, an alternating block, or
its intrinsic MS pair. The actual chief-count obstruction excludes the block.
In the MS case the canonical characteristic reduction and its core equality
recover that same block. Thus only the characteristic subgroup remains,
whose normalizer is controlled by the original maximal-local hypothesis.

All line selection, small Thompson image, and characteristic-normal cases
are discharged here. The one explicit premise is the core equality on the
canonical reduced source; its producers are the MS93 critical-distance
branches. The final bound concerns exactly B(O₂(L₁T)).

Source: Aschbacher--Smith 13.7.4(1), via C.1.37 and C.1.32;
MS93 Sections 3 and 5.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
open CFSG.Quasithin.ChapterC CFSG.Quasithin.ChapterC.NaturalSixControl
open Section08.SourceCompletion Section05.PlaneGeometry
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
local notation "X" => (L ⊔ (T : Subgroup G) : Subgroup G)
local notation "LX" => L.subgroupOf X

theorem source_baumann_normalizer_le_of_reduced_core
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hcore : let := component_normal d
             let := local_module_normal d
             ∀ (v : V₁) (hv : v ≠ 1)
               (hm : IntrinsicMSPair (sourceData d h hU hV v hv)),
               let s := SymplecticSetup.SourceData.originalSource
                 (sourceData d h hU hV v hv) hm
               BinaryMS.MS93.core s.reduction.radical (BinaryMS.MS93.alpha s.reduction.radical) =
                 BinaryMS.MS93.U s.reduction.radical (BinaryMS.MS93.alpha s.reduction.radical)) :
    normalizer (ChapterB.baumann
      ((sourceOne L T V₁ ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2) : Set G) ≤ M := by
  let := component_normal d
  let := local_module_normal d
  have hnV : Nontrivial V₁ := Finite.one_lt_card_iff_nontrivial.mp (by rw [d.line_card]; decide)
  obtain ⟨v,hv⟩ := exists_ne (1 : V₁)
  let d0 := sourceData d h hU hV v hv
  rcases d0.characteristic_or_block_or_intrinsicMSPair with hc | hb | hm
  · obtain ⟨C,hC,hne,hn⟩ := hc
    exact sourceData_characteristic_normalizer_bound d h hU hV v hv h1221 C hC hne hn
  · exact (source_not_alternatingBlock d h hU hV hb).elim
  · let s := SymplecticSetup.SourceData.originalSource d0 hm
    have he := hcore v hv hm
    have hb := SymplecticSetup.SourceData.ms_block_of_reduced_core_eq_U d0 hm s.reduction he
    exact (source_not_alternatingBlock d h hU hV hb.2).elim

end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
