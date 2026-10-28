module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OrdinaryAssembly
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryBlocksAt
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.CompleteAt

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseAssembly
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryBaumannSource
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinarySourceEscape
public import CFSG.Quasithin.Chapter13.Section05.AmbientSource.ParabolicCentralizer

/-!
# The actual ordinary terminal consumer from local source inputs

The guarded 12.2.13 theorem uses only the original structural and module
inputs at G,T. Its escape applies to the unchanged chosen natural module;
the completed ordinary block geometry proves plane noncentrality. The complete local
ordinary source chain supplies the full abelian span, G₁ in the original Hz
family, and F.9. Thus the terminal denominator cases use the same critical
pairs, literal filtration maps and marked point-normalizer images.

The center comparison excludes the covered alternative only for this ordinary
L/O₂(L) ≃ A₆ quotient. It does not discharge the covered branch of 13.8.1.
Component supplements and the later 13.8.27/33 and denominator/point models
remain explicit with the existing producers of qt-d-1381-source. Earlier
structural/module inputs and natural choice remain with qt-d-1222-source
and qt-d-1332-source. The completed qt-d-13314-ordinary-blocks proof is used
through its local adapters, leaving no block or plane callback here.
Final source discharge is retained by qt-d-1378-source and qt-d-1381-source.

Source: Aschbacher–Smith 13.3.14,13.7.8,13.8.1–8,27,33–34,
printed pp.891–893,940–949,963,966–969; maximal selection, p.1079.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OrdinaryAssembly
open CriticalGeometry
open TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix
open Chapter14.Section08.LieTypeBranch

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}

/-- The final ordinary branch on the actual maximal source data. The
preceding stage assumptions expose their concrete outputs and are still
to be proved by their source owners. Neither F.9, abelianness, an Hz choice,
H = G₁, the ambient centralizer bound nor a critical pair is assumed. -/
theorem contradiction_of_original_source_stages_at
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (modules1222 : Chapter12.Section02.Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (component : ∃ K : Subgroup G,
      G₁ = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)) ∧
      (K.subgroupOf G₁).IsCComponent ∧ (K.subgroupOf G₁).Normal ∧
      IsQuasisimple (Source.starImage G₁ K))
    (alternatives : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∨
      ∃ hU : IsElementaryAbelian 2 (Source.UH G₁ V₃), letI := hU
        TerminalRanks.MarkedModels G₁ ((L ⊔ (T : Subgroup G)) ⊓ G₁) V₃ V₁)
    (case_one : ∀ c : CriticalPair L (T : Subgroup G) G₁ V,
      (Source.DH (Source.UH G₁ V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH G₁ V₃ ∨
        Source.Dgamma (c.Ugamma V₃) (Source.UH G₁ V₃) V₁ = c.Ugamma V₃) →
      CaseAssembly.CaseOneModels T L G₁ V₃ V V₁)
    (point_models : ∀ c : CriticalPair L (T : Subgroup G) G₁ V,
      Source.DH (Source.UH G₁ V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH G₁ V₃ →
      Source.Dgamma (c.Ugamma V₃) (Source.UH G₁ V₃) V₁ < c.Ugamma V₃ →
      c.Aone V₁ ≤ Source.UH G₁ V₃ →
      Nonempty (Source.starImage G₁ (normalizer (c.Aone V₁ : Set G)) ≃* a6DuadStabilizer) ∨
        Nonempty (Source.starImage G₁ (normalizer (c.Aone V₁ : Set G)) ≃* duadStabilizer)) :
    False := by
  have escape := Chapter12.Section02.RecognitionSource.theorem12213_of_modules_of_many_at
    structural modules1222 hmany
  have hm := Section03.Noncentrality.ordinary_plane_noncentral_of_original_source_at
    d hmax eL escape h1332 fixed modules
  obtain ⟨hHz,hspan,hall⟩ := original_six_selected_source_inputs_at d hmax eL hm
    h1332 modules escape
  let dl := d.toLocalSetup hspan
  have hF9 := (hall G₁ hHz).1
  have hcentral := Section05.AmbientSource.source_parabolic_centralizer d eL
    (hypothesis1221_of_maximal_natural_six d hmax eL)
    (by rwa [← d.first_normalizer])
  have hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥ := by
    intro he
    apply hm
    apply bot_unique
    rw [commutator_comm] at he
    exact (commutator_mono le_rfl d.plane_le_seed).trans_eq he
  obtain ⟨K, hgen, hK, hN, hqs⟩ := component
  rcases alternatives with hcover | ⟨hU, hmodels⟩
  · exact not_covered_local_quotient eL hcover
  · exact CaseAssembly.contradiction_of_source_cases dl hHz hF9 rfl
      hgen hK hN hqs hcentral hcomm hmodels case_one point_models

/-- Select one original natural module and flag, discharge guarded recognition,
and supply every ordinary Section 13.8 opening output on that same choice.
The block proof is supplied; the natural marking and original local module
clauses retain their earlier source producers. -/
theorem exists_selected_source_inputs_of_original_modules_of_many_at
    (hmax : Maximal (Counterexample T) L)
    (natural : ∃ V : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T L V) ∧
      (T : Subgroup G) ≤ normalizer (V : Set G) ∧
      Chapter6.Source.IsConjugationModel L V
        (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)))
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Chapter13.Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (modules1222 : Chapter12.Section02.Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L) :
    ∃ V V₁ V₂ V₃ : Subgroup G,
      Nonempty (NaturalSetup T L V V₁ V₂ V₃
        (normalizer (L : Set G)) (normalizer (V₁ : Set G))) ∧
      normalizer (V₁ : Set G) ∈ Chapter13.Section08.Source.Hz (sourceOne L T V₁) T
        (normalizer (V₁ : Set G)) (normalizer (L : Set G)) ∧
      IsMulCommutative (conjugateSpanBy V (normalizer (V₁ : Set G))) ∧
      ∀ H ∈ Chapter13.Section08.Source.Hz (sourceOne L T V₁) T
          (normalizer (V₁ : Set G)) (normalizer (L : Set G)),
        (Chapter13.Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis ∧
        IsMulCommutative (Chapter13.Section08.Source.VH H V) ∧
        ∃ c : Chapter13.Section08.CriticalGeometry.CriticalPair L (T : Subgroup G) H V,
          Odd c.path.length ∧
          Chapter13.Section08.CriticalGeometry.Reorientation.EarlierGeometry c V₃ V₁ ∧
          ¬ ⁅c.Ugamma V₃,V⁆ ≤ c.Aone V₁ :=
  Section03.Noncentrality.exists_ordinary_selected_source_inputs_of_original_source_at
    hmax natural
    (Chapter12.Section02.RecognitionSource.theorem12213_of_modules_of_many_at
      structural modules1222 hmany) h1332 fixed modules

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OrdinaryAssembly
