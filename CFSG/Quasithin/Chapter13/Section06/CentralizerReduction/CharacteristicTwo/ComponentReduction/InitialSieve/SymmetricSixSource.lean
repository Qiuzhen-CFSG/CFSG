module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.CompleteSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.SymmetricSix
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralNormality
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.Source
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFiveCentralizer

/-!
# Eliminating the whole S6 quotient in 13.6.6

The actual earlier A3.8 orbit/model source instantiates the central-cover
and residual A4 recognition on the prescribed component. The marked core
commutator identifies U(L) with V. The proved five-block splitting then
gives O2(LT)=V, so the original 3.2.11 argument makes V self-centralizing.
The preceding abelian conjugate span and escaping singular centralizer
contradict this. No universal block certificate or model-sieve premise is
required. The final consumer retains exactly the earlier local and marked
module hypotheses; it does not yet assert characteristic two of C_G(v).

Source: Aschbacher--Smith, proof of 13.6.6, printed p.927.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve
open A5Module ChapterC
open scoped IsMulCommutative
universe u

/-- Instantiate the full earlier orbit/model theorem from its genuine source producers. -/
theorem earlierConjugates_knownSimple : EarlierConjugates KnownSimple.IsKnownSimple := by
  intro H _ _ hH hcore B hB
  by_cases hn : B.Normal
  · exact Or.inl hn
  have hquasi := (ChapterA.Section03.NoncentralNormality.normal_or_quasisimple hH hcore hB).resolve_left hn
  exact Or.inr (ChapterA.SQTKStructure.NonnormalOuterSource.nonnormal_component_index_and_model
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    hH hcore B ⟨hB.subnormal, hquasi⟩ hn)

namespace SymmetricSix
variable {G : Type u} [Group G] [Finite G] {L V M : Subgroup G}
  {T : Sylow 2 G} {s : Marking L V}

/-- The actual A4 residual identifies U(L) with the marked V; the genuine
five-block split therefore identifies the whole core O2(LT) with V. -/
theorem SourceData.core_eq_of_residual_A4 (d : Setup KnownSimple.IsKnownSimple T s)
    (h : SourceData d M) (e : Lv L (markedV s) ≃* alternatingGroup (Fin 4)) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 = V := by
  have hbound := BlockRecognition.core_commutator_bound s h.moduleData e
  have hb := BlockRecognition.alternatingBlock_of_commutator_bound s h.moduleData hbound
  have hU : (blockU L).map L.subtype = V := by
    rw [BlockRecognition.blockU_eq_marked s h.moduleData hbound]
    exact map_subgroupOf_eq_of_le d.V_le_L
  have hsplit := hb.normalizer_twoCore_eq_module_sup_centralizer
    (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
    (sup_le L.le_normalizer h.T_normalizes)
  have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow (L ⊔ (T : Subgroup G))
      (T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right))
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using hh
  have hc : (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer (L : Set G) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right _ hQT).trans_eq (h.centralizer_T d))
  simpa only [hU, hc, sup_bot_eq] using hsplit

/-- The initial S6 branch is impossible from the preceding original source
configuration; neither universal C113c nor a block conclusion is an input. -/
theorem SourceData.not_symmetricSix_knownSimple (d : Setup KnownSimple.IsKnownSimple T s)
    (h : SourceData d M) (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K) (a : ActionData s (T : Subgroup G) K) :
    ¬ Nonempty (XStar K ≃* Equiv.Perm (Fin 6)) := by
  rintro ⟨e⟩
  obtain ⟨e4⟩ := residual_isA4 d h.moduleData earlierConjugates_knownSimple d.oddCore_eq_bot K hK a e
  have he := h.core_eq_of_residual_A4 d e4
  let := marking_commutative s
  have hcore := Chapter3.Section02.lemma_3_2_11_of_core_containment T L
    (L ⊔ (T : Subgroup G)) M V le_sup_right (h.LT_le_M d)
    (le_sup_left.trans (h.LT_le_M d)) (h.M_eq_normalizer d) h.maximal h.characteristic_two
    he.symm h.moduleData.V_le_core (marking_nontrivial s)
  let := h.abelian_span
  exact not_selfCentralizing_of_abelian_span V M (markedZ s) h.z_outside h.normalizer_V
    hcore.2.2.1.le

/-- The original initial component analysis leaves only a field of size greater
than two and places its actual central four-group inside the component image. -/
theorem SourceData.largeField_knownSimple (d : Setup KnownSimple.IsKnownSimple T s)
    (h : SourceData d M) (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K) :
    ∃ a : ActionData s (T : Subgroup G) K, LargeField K a := by
  obtain ⟨a,ha⟩ := source_model_sieve d K hK
  exact ⟨a,ha.resolve_right (h.not_symmetricSix_knownSimple d K hK a)⟩
end SymmetricSix
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open Subgroup Theory.GroupTheory A5Module ComponentReduction InitialSieve
open InitialSieve.SymmetricSix
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

/-- Construct the original local inputs of the S6 contradiction from the same
marked configuration; the module kernel/core properties are earlier source data. -/
theorem LocalConfiguration.symmetricSixSource
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (e : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (c : LocalConfiguration (normalizer (L : Set G)) d.flag)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hm : ModuleData d.flag.module) :
    SourceData (c.initialSetup hG (hm.V_le_core.trans (map_subtype_le _)) d.V_le_T)
      (normalizer (L : Set G)) := by
  have hM : IsMaximalTwoLocal (normalizer (L : Set G)) ∧
      L ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) := by
    have hh := Set.mem_singleton (normalizer (L : Set G))
    rw [← e.maximal_overgroups] at hh
    exact hh
  refine ⟨hm, e.T_normalizes_L, ?_, hM.1,
    hG.evenCharacteristic T _ hM.1 (le_sup_right.trans hM.2), ?_, ?_,
    c.reductions.centralizer_outside, e.module_normalizer, c.reductions.abelian_span⟩
  · have he : fundamentalClosure L (T : Subgroup G) = L :=
      le_antisymm (conjugateSpanBy_le le_rfl e.T_normalizes_L) (le_conjugateSpanBy _ _)
    rw [he]
  · intro N hN hle
    have hh : N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N} :=
      ⟨hN, hle⟩
    rw [e.maximal_overgroups] at hh
    exact hh
  · have hh : Minimal (fun H : Subgroup G =>
        H ∈ Chapter1.HOver G (T : Set G) ∧ ¬ H ≤ normalizer (L : Set G))
        c.reductions.outsideLocal := c.reductions.outside_mem
    exact ⟨c.reductions.outsideLocal, hh.prop.2,
      e.outside_centralizes _ c.reductions.outside_mem⟩

/-- The original earlier-source consumer after the S6 contradiction: any
component in C_G(v) has an actual field exponent greater than one and E*≤K*. -/
theorem large_field_component_of_earlier_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (e : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hm : ModuleData d.flag.module)
    (hcounter : IsA5Counterexample G) (hfusion : ControlsFusionOfZ d.flag.module)
    (hnot : generalizedFitting (Gv (markedV d.flag.module)) ≠
      pCore 2 (Gv (markedV d.flag.module))) :
    ∃ K : Subgroup (Gv (markedV d.flag.module)),
      IsComponent (Gv (markedV d.flag.module)) K ∧
      ∃ a : ActionData d.flag.module (T : Subgroup G) K, LargeField K a := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃ e hcounter hfusion
  let ds := c.initialSetup hG (hm.V_le_core.trans (map_subtype_le _)) d.V_le_T
  have hsource := c.symmetricSixSource d V₃ e hG hm
  obtain ⟨K,hK⟩ := exists_component_of_not_characteristic_two d.flag.module
    (fun x hx => ds.local115.inverts_oddCore x hx) hnot
  exact ⟨K,hK,hsource.largeField_knownSimple ds K hK⟩
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
