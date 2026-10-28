module
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryBlockContainingAt
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.ModuleSieve.ChosenClosure
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.ModuleSieve.Surviving
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.EarlierModules

/-!
# The original block module sieve with local 13.3.2 inputs

The fixed-module clause at the original Hypothesis 13.3.1 excludes containment
of the point residual in the selected component. Its literal quotient is then
A₅. The original chosen module gives the A₅ marking using only that faithful
local component, and the simple quotient identifies the same offender image.
Both original local module clauses remain with qt-d-1332-source; no universal
classification is inferred from these premises.
Source: Aschbacher–Smith 13.3.2(3),13.3.14(g), pp.885,892–893.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open ChapterB.SourceInduction ChapterB.QuasisimpleSource Chapter12.Section02
open Representation.BinaryOffender.Homogeneous
open Section08.SourceCompletion Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
include d

theorem ordinary_reduction_g_of_fixed_module_source_at
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (fixed : Chapter13.Section03.SourceCompletion.OriginalFixedModule1332At T L) (hc : ⁅H.pCoreIn 2,E⁆ = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T) :
    ¬ sourceOne L T P ≤ K.map H.subtype := by
  intro hAK
  obtain ⟨D⟩ := ordinary_containing_moved_module_chosen_at d hmax eL escape h1332 hc K hK hqK hf hAK
  obtain ⟨e⟩ := fixed (Chapter14.Section03.FaithfulSource.hypothesis1331 d.counterexample) _ hf _ D
    (ordinary_movedModule_fixed_ne_bot_of_actor_le d eL h1332 hc K hK hqK hf hAK)
  exact ordinary_containing_core_action_contradiction d eL h1332 hc K hK hqK hf hAK D e

theorem ordinary_selected_five_quotient_of_fixed_module_source_at
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (fixed : Chapter13.Section03.SourceCompletion.OriginalFixedModule1332At T L) (hc : ⁅H.pCoreIn 2,E⁆ = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hn : (sourceOne L T P).subgroupOf H ≤ normalizer (K : Set H))
    (hgen : ⁅K,(sourceOne L T P).subgroupOf H⁆ = K) :
    (¬ sourceOne L T P ≤ K.map H.subtype) ∧
      Nonempty ((K.map H.subtype ⧸ pCore 2 (K.map H.subtype)) ≃*
        alternatingGroup (Fin 5)) := by
  have hnot := ordinary_reduction_g_of_fixed_module_source_at d hmax eL escape h1332 fixed
    hc K hK hqK hf
  exact ⟨hnot,ordinary_selected_five_quotient_of_noncontainment d eL h1332
    K hK hqK hf hn hgen hnot⟩

theorem ordinary_selected_moved_model_of_irrPlus_at
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (fixed : Chapter13.Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Chapter13.Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (hc : ⁅H.pCoreIn 2,E⁆ = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hn : (sourceOne L T P).subgroupOf H ≤ normalizer (K : Set H))
    (hgen : ⁅K,(sourceOne L T P).subgroupOf H⁆ = K)
    (hi : let J := Diagonal.localGroup (K.map H.subtype) (sourceOne L T P) T
      IsIrrPlus (reducedRepresentation J) ((K.map H.subtype).subgroupOf J)
        (moved (reducedRepresentation J) ((K.map H.subtype).subgroupOf J))) :
    (¬ sourceOne L T P ≤ K.map H.subtype) ∧
      Chapter6.Source.IsConjugationModel (K.map H.subtype)
        (Diagonal.movedModule (K.map H.subtype) (sourceOne L T P) T)
        Chapter6.Source.a5Module := by
  obtain ⟨hout,hfive⟩ := ordinary_selected_five_quotient_of_fixed_module_source_at d hmax eL escape
    h1332 fixed hc K hK hqK hf hn hgen
  obtain ⟨D⟩ := ordinary_selected_chosen_of_moved_irrPlus d h1332 K hqK hf hi
  exact ⟨hout,five (Chapter14.Section03.FaithfulSource.hypothesis1331 d.counterexample) _ hf hfive _ D⟩

omit d in
private theorem simple_core_image_equiv
    {D Q : Type*} [Group D] [Group Q] (B : Subgroup D) (q : D →* Q)
    (hs : IsSimpleGroup (B ⧸ pCore 2 B))
    (hk : B.pCoreIn 2 ≤ q.ker) (hne : B.map q ≠ ⊥) :
    Nonempty ((B ⧸ pCore 2 B) ≃* B.map q) := by
  let f := q.subgroupMap B
  have hker : pCore 2 B ≤ f.ker := by
    intro b hb
    apply Subtype.ext
    exact hk (mem_map_of_mem B.subtype hb)
  let φ := QuotientGroup.lift (pCore 2 B) f hker
  have hsurj : Function.Surjective φ :=
    QuotientGroup.lift_surjective_of_surjective _ _ (q.subgroupMap_surjective B) _
  let := hs
  have hinj : Function.Injective φ := by
    apply φ.ker_eq_bot_iff.mp
    rcases φ.normal_ker.eq_bot_or_eq_top with hb | ht
    · exact hb
    · have hφ : φ = 1 := φ.ker_eq_top_iff.mp ht
      apply False.elim
      apply hne
      apply (eq_bot_iff_forall _).mpr
      intro b hb
      obtain ⟨x,hx⟩ := hsurj ⟨b,hb⟩
      have he := congrArg Subtype.val hx
      simpa only [hφ,MonoidHom.one_apply,OneMemClass.coe_one] using he.symm
  exact ⟨MulEquiv.ofBijective φ ⟨hinj,hsurj⟩⟩

theorem ordinary_selected_offender_component_five_at
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (fixed : Chapter13.Section03.SourceCompletion.OriginalFixedModule1332At T L) (hc : ⁅H.pCoreIn 2,E⁆ = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hn : (sourceOne L T P).subgroupOf H ≤ normalizer (K : Set H))
    (hgen : ⁅K,(sourceOne L T P).subgroupOf H⁆ = K) :
    let B := K.map H.subtype
    let J := Diagonal.localGroup B (sourceOne L T P) T
    let W := reducedTwoSubgroup J
    letI := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
    let C := centralizer (W : Set J)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let N := offenderSubgroup ρ
    Nonempty ((((B.subgroupOf J).map q).subgroupOf N) ≃* alternatingGroup (Fin 5)) := by
  let B := K.map H.subtype
  let J := Diagonal.localGroup B (sourceOne L T P) T
  let W := reducedTwoSubgroup J
  let := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
  let C := centralizer (W : Set J)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let N := offenderSubgroup ρ
  let BJ := B.subgroupOf J
  have hBJ : B ≤ J := le_sup_left.trans le_sup_left
  have hTH : (T : Subgroup G) ≤ H := d.first_normalizer ▸ d.line_stable
  have hJH : J ≤ H := sup_le
    (sup_le (map_subtype_le _) (ordinary_point_residual_le_point d)) hTH
  let : K.Normal := ordinary_component_normal d h1332 K hK hf
  have hBN : H ≤ normalizer (B : Set G) := by
    have hh := K.le_normalizer_map H.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  let : BJ.Normal := normal_subgroupOf_of_le_normalizer (hJH.trans hBN)
  obtain ⟨hBq,hcomp,_⟩ :=
    ordinary_selected_offender_entry_of_original_source_at d hmax eL escape h1332 K hK hqK hf
  obtain ⟨_,⟨eB⟩⟩ := ordinary_selected_five_quotient_of_fixed_module_source_at d hmax eL escape
    h1332 fixed hc K hK hqK hf hn hgen
  let eBJ : BJ ≃* B := subgroupOfEquivOfLe hBJ
  let eQ := (QuotientGroup.congr _ _ eBJ (pCore_map_iso 2 eBJ)).trans eB
  have hs : IsSimpleGroup (BJ ⧸ pCore 2 BJ) := by
    let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    exact eQ.isSimpleGroup
  have hne : BJ.map q ≠ ⊥ := by
    intro he
    apply hcomp.isCComponent.ne_bot
    change (BJ.map q).subgroupOf N = ⊥
    rw [he,bot_subgroupOf]
  have hk : BJ.pCoreIn 2 ≤ q.ker := by
    rw [QuotientGroup.ker_mk']
    exact normal_pCore_le_centralizer_reducedPSubgroup 2 BJ
  obtain ⟨ei⟩ := simple_core_image_equiv BJ q hs hk hne
  exact ⟨(subgroupOfEquivOfLe hBq).trans (ei.symm.trans eQ)⟩

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
