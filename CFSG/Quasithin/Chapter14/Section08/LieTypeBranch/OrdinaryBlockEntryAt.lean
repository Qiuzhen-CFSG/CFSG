module
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinarySourceEscapeAt
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.BaumannBudget.CompletedBudget

/-!
# Local source entry and chief budget for the original ordinary blocks

Use the original maximal choice and its point-normalizer escape at G,T to
enter the reduced offender classification. The completed diagonal Baumann
identity then gives Baumann escape, and the existing natural-six block
alternative bounds every full chief series of the same point residual.
The literal block consumer uses this bound to identify the original moved
module with U(K); no nonabelian full-span hypothesis is introduced.
These proofs reuse the completed qt-d-13314-ordinary-blocks chain.
Source: Aschbacher–Smith 13.3.10(2),13.3.14(e–g), pp.887–888,892–893.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open ChapterB.SourceInduction ChapterB.QuasisimpleSource Chapter12.Section02
open Chapter14.Section08.LieTypeBranch NoncentralChiefRefinement
open Representation.BinaryOffender.Homogeneous
open Section08.SourceCompletion Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
include d

theorem ordinary_selected_offender_entry_of_original_source_at
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    (original_six_point_normalizer_mem_Hz_at d hmax eL escape).2.2 h1332 K hK hqK hf

theorem ordinary_selected_block_layer_of_original_budget_at
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hmax : Maximal (Counterexample T) L)
    (escape : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    (original_six_point_normalizer_mem_Hz_at d hmax eL escape).2.2
    h1332 K hK hqK hf hm hn hgen hcount

theorem ordinary_baumann_escape_of_core_identity_at
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hB : ChapterB.baumann ((sourceOne L T P ⊔ (T : Subgroup G)).pCoreIn 2) =
      ChapterB.baumann ((K.map H.subtype ⊔ (T : Subgroup G)).pCoreIn 2)) :
    ¬ normalizer (ChapterB.baumann
      ((sourceOne L T P ⊔ (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M := by
  have hout := (ordinary_component_normalizer_conclusions_of_escape d
    (Chapter14.Section08.LieTypeBranch.hypothesis1221_of_maximal_six hmax eL)
    (Chapter14.Section08.LieTypeBranch.original_six_point_normalizer_mem_Hz_at d hmax eL escape).2.2
    h1332 K hK hf).2.2.2.2.2
  let J := K.map H.subtype ⊔ (T : Subgroup G)
  have hn : K.map H.subtype ≤ normalizer (ChapterB.baumann (J.pCoreIn 2) : Set G) :=
    (show K.map H.subtype ≤ J from le_sup_left).trans
      ((J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))).trans
        (Stellmacher.normalizer_le_normalizer_baumann _))
  rw [hB]
  exact fun hh => hout (hn.trans hh)

theorem ordinaryBlockSource_of_module_and_chief_sources_at
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (escape : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (rows : OrdinaryMovedModuleSource d) (chief : OrdinaryChiefBudgetSource d) :
    OrdinaryBlockSource d := by
  intro K hK hKs hm hn hgen hq hU hf
  obtain ⟨hout,hmodel⟩ := rows K hK hKs hm hn hgen hq hU hf
  have hcount := chief K hK hKs hm hn hgen hq hU hf hout hmodel
  obtain ⟨hbound,hlayer⟩ := ordinary_selected_block_layer_of_original_budget_at d eL hmax escape
    h1332 K hK hq hf hm hn hgen hcount
  have hfaith := (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T _).mp hf
  have hblock := ordinary_alternatingBlock_of_moved_model _ _ _
    hfaith.2.1.2.1 hfaith.2.1.2.2 hlayer hmodel
  exact ⟨hblock,hout,hbound⟩

/-- The original diagonal Baumann identity and A₆ block alternative give the
chief budget using only recognition at the original G,T. -/
theorem ordinaryChiefBudgetSource_of_original_source_at
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : SupercriticalSource.Source1332OneTwo T) : OrdinaryChiefBudgetSource d := by
  intro K hK hKs hm hn hgen hq hU hf hout hmodel s h0 h1
  have he := ordinaryBaumannIdentitySource_of_original_source d eL h1332
    K hK hKs hm hn hgen hq hU hf hout hmodel
  have hescape := ordinary_baumann_escape_of_core_identity_at d hmax eL escape h1332 K hK hf he
  exact ordinary_chief_count_le_two_of_block d eL
    (ordinaryBaumannBlockAlternative_of_original_source d hmax eL hescape) s h0 h1

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
