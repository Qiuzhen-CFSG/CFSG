module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.CoreGeometry
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinarySourceEscape

/-!
# The original ordinary source enters the reduced offender classification

The actual maximal A₆ choice supplies Hypothesis 12.2.1. Source 12.2.13
supplies escape of its prescribed point normalizer; the escape-based
Thompson argument then applies to each literal selected component.
No assumption on the full V-span is used. The earlier universal escape
and faithful-family theorems retain their separate source producers.

Source: Aschbacher--Smith, 13.3.14(e--g), printed pp.892--893.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section08.LieTypeBranch
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
include d

/-- The literal original B.5 entry from maximality and source escape. -/
theorem ordinary_selected_offender_entry_of_original_source
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T) :
    let B := K.map H.subtype
    let J := Diagonal.localGroup B (sourceOne L T P) T
    let W := reducedTwoSubgroup J
    letI := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
    let C := centralizer (W : Set J)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let N := offenderSubgroup ρ
    (B.subgroupOf J).map q ≤ N ∧
      IsComponent N (((B.subgroupOf J).map q).subgroupOf N) ∧
      ChapterB.SourceInduction.NontrivialAdequateAlternative (ρ.comp N.subtype) :=
  ordinary_selected_offender_entry_of_escape d
    (hypothesis1221_of_maximal_six hmax eL)
    (original_six_point_normalizer_mem_Hz d hmax eL escape).2.2 h1332 K hK hqK hf

/-- The original maximal choice converts its chief budget into the two actual
core conclusions used by block recognition. The budget is the separate Baumann step. -/
theorem ordinary_selected_block_layer_of_original_budget
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hmax : Maximal (Counterexample T) L)
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hm : ⁅K.map (QuotientGroup.mk' (pCore 2 H)),
      (star H (sourceOne L T P) (ordinary_point_residual_le_point d)).pCoreIn 2⁆ ≠ ⊥)
    (hn : (sourceOne L T P).subgroupOf H ≤ normalizer (K : Set H))
    (hgen : ⁅K,(sourceOne L T P).subgroupOf H⁆ = K)
    (hcount : ∀ s : ChiefSeries (sourceOne L T P),
      s.head = ⊥ → s.last = ⊤ → s.noncentralTwoCount ≤ 2) :
    ⁅(Diagonal.localGroup (K.map H.subtype) (sourceOne L T P) T).pCoreIn 2,
      sourceOne L T P⁆ ≤ Diagonal.movedModule (K.map H.subtype) (sourceOne L T P) T ∧
    (ChapterC.blockU (K.map H.subtype)).map (K.map H.subtype).subtype =
      Diagonal.movedModule (K.map H.subtype) (sourceOne L T P) T :=
  ordinary_selected_block_layer_of_chief_budget d eL
    (hypothesis1221_of_maximal_six hmax eL)
    (original_six_point_normalizer_mem_Hz d hmax eL escape).2.2
    h1332 K hK hqK hf hm hn hgen hcount

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
