module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.OriginalCoreComplete
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.Control
/-!
# The original Baumann normalizer bound from the full source pair

The original natural-six pair satisfies the characteristic-or-block alternative
with its native symplectic core premise discharged. The chief-count theorem
excludes the alternating block. The remaining nontrivial normal characteristic
subgroup therefore gives the required normalizer bound on the original Baumann
subgroup.

Source: Aschbacher--Smith13.7.4(1), using the native MS93 symplectic argument.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
open CFSG.Quasithin.Chapter13 CFSG.Quasithin.ChapterC
open CFSG.Quasithin.ChapterC.NaturalSixControl
open Section08.SourceCompletion Section05.PlaneGeometry
open Section08.TransvectionRecognition.Component.ModelExtension
open BinaryMS.MS93
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

theorem source_baumann_normalizer_le
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬IsMulCommutative (Section08.Source.VH H V)) :
    normalizer (ChapterB.baumann
      ((sourceOne L T V₁⊔(T:Subgroup G):Subgroup G).pCoreIn 2):Set G)≤M := by
  let := component_normal d
  let := local_module_normal d
  have hnV : Nontrivial V₁ := Finite.one_lt_card_iff_nontrivial.mp
    (by rw [d.line_card]; decide)
  obtain ⟨v,hv⟩ := exists_ne (1 : V₁)
  let d0 := sourceData d h hU hV v hv
  rcases d0.characteristic_or_block_source with hc | hb
  · obtain ⟨C,hC,hne,hn⟩ := hc
    exact sourceData_characteristic_normalizer_bound d h hU hV v hv h1221 C hC hne hn
  · exact (source_not_alternatingBlock d h hU hV hb).elim
end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
