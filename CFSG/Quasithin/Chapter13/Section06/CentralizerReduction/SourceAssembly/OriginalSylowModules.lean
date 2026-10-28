module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.OriginalSylowNormalization
public import CFSG.Quasithin.Chapter13.Section03.SourceClassification.OriginalAlternatingFiveFromRowsAt
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.SourceReplacement

/-!
# Original A₅ modules at every ambient Sylow

The uniform A₅ clause supplies both the quasisimple and model inputs of
the proved original module-row adapter. Thus the actual Chapter 12 module
rows at a Sylow give the original A₅ module clause there, before any Context
has been chosen. The proved normalization source then constructs that Context.

Starting with one original Context, its faithful A₅ quotient marks transport
to every Sylow. The guarded module-row family is applied separately at each
such Sylow; no module-classification premise is transported from the initial
Sylow. This supplies the literal Context family used by the replacement
component and omega-centralizer arguments.

Source: Aschbacher--Smith 12.2.2(3d),13.3.1(4),13.3.2(3), pp.795,884--885.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.SourceClassification Section03.SourceCompletion
open Section03.A5Setup.OriginalMaximality Section05.A5Source
open Chapter1.Section02.Adequate
open ComponentSelection ComponentElimination.SourceContainment.RankTwo.LocalApplication
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- The original uniform A₅ hypothesis supplies the catalogue premises of
the actual chosen-module row adapter, without structural or exit inputs. -/
theorem original_five_modules_of_module_rows
    (h : Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T) :
    OriginalAlternatingFiveModules1332At T L := by
  apply originalAlternatingFiveModules1332At_of_module_rows _ _ modules
  · intro K hK
    have hf : K ∈ MainForward.faithfulLocalComponents T :=
      (mem_faithfulLocalComponents_iff T K).mpr ⟨hK.1.1,hK.2⟩
    obtain ⟨eK⟩ := h.five_minimal ⟨e⟩ K hf
    let hK' : Hypothesis1331 T K :=
      { h with local_component := hf
               five_minimal := fun _ => h.five_minimal ⟨e⟩ }
    exact (hypothesis1221 hK' eK).quasisimple
  · intro K hK
    exact Or.inl (h.five_minimal ⟨e⟩ K
      ((mem_faithfulLocalComponents_iff T K).mpr
        ⟨hK.maximal_faithful.1.1,hK.maximal_faithful.2⟩))

/-- Construct the initial actual Context directly from the original A₅
source and the module rows at its own Sylow. -/
theorem exists_context_from_original_module_rows
    (h : Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T) :
    ∃ V V₁ V₂ V₃ : Subgroup G, V₂ ≤ V₃ ∧
      Nonempty (Context T L V V₁ V₂ V₃) :=
  exists_context_from_original_modules h e hmany
    (original_five_modules_of_module_rows h e modules)

/-- Apply the guarded Chapter 12 rows at every actual Sylow. The quotient
marks come from the original Context, while the module rows stay at S. -/
theorem original_modules_at_every_sylow
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (modules : ∀ S : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard →
        Theorem1222ModulesAt KnownSimple.IsKnownSimple S) :
    ∀ (S : Sylow 2 G) (I : Subgroup G), OriginalAlternatingFiveModules1332At S I := by
  intro S I h
  obtain ⟨e⟩ := original_faithful_A5_at_every_sylow d S I h.local_component
  have hm : 1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard := by
    rwa [maximalTwoLocalOvergroups_ncard_sylow S T]
  exact original_five_modules_of_module_rows h e (modules S hm) h

/-- The literal replacement Context family, with all module choices made
at the replacement Sylow and with its transported standing guard. -/
theorem original_contexts_at_every_sylow
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (modules : ∀ S : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard →
        Theorem1222ModulesAt KnownSimple.IsKnownSimple S) :
    ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃) := by
  intro S I standing
  have hm : 1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard := by
    rwa [maximalTwoLocalOvergroups_ncard_sylow S T]
  obtain ⟨e⟩ := standing.a5
  obtain ⟨W,W₁,W₂,W₃,_,he⟩ := exists_context_from_original_modules
    (sourceHypothesis_hypothesis1331 standing) e hm
    (original_modules_at_every_sylow d hmany modules S I)
  exact ⟨W,W₁,W₂,W₃,he⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
