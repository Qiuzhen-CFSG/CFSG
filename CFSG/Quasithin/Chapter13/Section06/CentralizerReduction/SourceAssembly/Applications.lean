module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.Local
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.OriginalContradiction
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.OriginalCatalogue

/-!
# Original nonsingular-centralizer assembly and its terminal application

The original A₅ Context supplies the aligned flag, relative normality,
Baumann alternatives and module data. Original 13.2.7 then supplies the
outside witness, Baumann normalizer bound and independent fusion argument.
The universal omega-centralizer theorem constructs 13.6.3 for every selected
component. Thus the surviving SL₄/SL₅ quotient catalogue feeds the proved
rank-four contradiction and yields both clauses of 13.6.7.

The terminal application uses the very same nonsingular mark and singular
escape. Original 13.3.2, 13.2.7 and the small-quotient selections remain
explicit source obligations; its independent 5.2.3 classifier is also explicit.
This is conditional assembly, not an unconditional source classification.

Source: Aschbacher–Smith 13.2.6–7, 13.6.1, 13.6.3, 13.6.7 and
13.6.22–23, printed pp.879–880,926,928,932–933.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open A5Module ComponentSelection ComponentReduction InitialSieve
open ComponentElimination.SourceContainment.RankTwo.LocalApplication
open Section05.A5Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

/-- Conditional source assembly of 13.6.7(1). The surviving small-model
producer is used only under failed containment, with the literal plus map.
All flag, local, module, fusion and universal 13.6.3 inputs are constructed.
The genuine 13.3.2, 13.2.7 and final small-model exclusions remain explicit. -/
theorem centralizer_le_of_context
    (hc : IsA5Counterexample G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h1327 : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∀ H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)),
        H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G))
    (hmodels : ¬ Gv (markedV d.flag.flag.module) ≤ normalizer (V : Set G) →
      ∀ K ∈ Yz L (T : Subgroup G) (markedZ d.flag.flag.module) (markedV d.flag.flag.module),
        Nonempty (plusImage K L (T : Subgroup G) (markedZ d.flag.flag.module)
          (markedV d.flag.flag.module) (normalizes_residual d) (centralizes_singular d) K ≃*
          SL(4,ZMod 2)) ∨
        Nonempty (plusImage K L (T : Subgroup G) (markedZ d.flag.flag.module)
          (markedV d.flag.flag.module) (normalizes_residual d) (centralizes_singular d) K ≃*
          SL(5,ZMod 2))) :
    Gv (markedV d.flag.flag.module) ≤ normalizer (V : Set G) := by
  by_contra hfail
  have ho := h1327 T L (standing d hc)
  have hB := baumann_normalizer d hc hmany ho
  have he := earlierLocal d hmany ho (baumann_alternatives d) hB
  obtain ⟨_,hf,hform⟩ := configuration_of_outside_source d hc hmany ho
  exact hfail (ComponentElimination.SourceOrthogonal.centralizer_le_normalizer_of_original_reduced_models
    d.flag V₃ he (standing d hc) (moduleData d) hf hform h1332
    (universal_omega_centralizer_of_original_outside_source T hmany h1332 h1327)
    (normalizes_residual d) (centralizes_singular d) (hmodels hfail))

/-- Apply the assembled nonsingular bound to both literal clauses of
13.6.7, retaining the original marked V_v and M=N_G(L). -/
theorem conclusions_of_context
    (hc : IsA5Counterexample G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h1327 : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∀ H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)),
        H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G))
    (hmodels : ¬ Gv (markedV d.flag.flag.module) ≤ normalizer (V : Set G) →
      ∀ K ∈ Yz L (T : Subgroup G) (markedZ d.flag.flag.module) (markedV d.flag.flag.module),
        Nonempty (plusImage K L (T : Subgroup G) (markedZ d.flag.flag.module)
          (markedV d.flag.flag.module) (normalizes_residual d) (centralizes_singular d) K ≃*
          SL(4,ZMod 2)) ∨
        Nonempty (plusImage K L (T : Subgroup G) (markedZ d.flag.flag.module)
          (markedV d.flag.flag.module) (normalizes_residual d) (centralizes_singular d) K ≃*
          SL(5,ZMod 2))) :
    Gv (markedV d.flag.flag.module) =
        normalizer (V : Set G) ⊓ Gv (markedV d.flag.flag.module) ∧
      normalizer (Vv L (markedZ d.flag.flag.module) (markedV d.flag.flag.module) : Set G) ≤
        normalizer (L : Set G) := by
  have hm := centralizer_le_of_context d hc hmany h1332 h1327 hmodels
  have hf := (configuration_of_outside_source d hc hmany (h1327 T L (standing d hc))).2.1
  exact centralizer_conclusions_of_containment L (normalizer (L : Set G)) V _ _ hm
    d.module_normalizer (normalizer_Vv_le_Gv_of_fusion d.flag.flag.module hf)

/-- The actual terminal A₅ consumer receives the same nonsingular bound
and singular escape. It retains only its independent earlier classifier
and the explicitly named source inputs of the centralizer assembly. -/
theorem terminal_model_of_context
    (hc : IsA5Counterexample G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h1327 : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∀ H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)),
        H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G))
    (hmodels : ¬ Gv (markedV d.flag.flag.module) ≤ normalizer (V : Set G) →
      ∀ K ∈ Yz L (T : Subgroup G) (markedZ d.flag.flag.module) (markedV d.flag.flag.module),
        Nonempty (plusImage K L (T : Subgroup G) (markedZ d.flag.flag.module)
          (markedV d.flag.flag.module) (normalizes_residual d) (centralizes_singular d) K ≃*
          SL(4,ZMod 2)) ∨
        Nonempty (plusImage K L (T : Subgroup G) (markedZ d.flag.flag.module)
          (markedV d.flag.flag.module) (normalizes_residual d) (centralizes_singular d) K ≃*
          SL(5,ZMod 2)))
    (h523 : TerminalContradiction.Components.SuzukiIsolation.Source523.EarlierTheorem.{u}
      KnownSimple.IsKnownSimple) : ClassificationModels.IsQTKEModel G := by
  apply TerminalContradiction.source_qtkeModel_of_A5_context d
    (centralizer_le_of_context d hc hmany h1332 h1327 hmodels) _ h523
  have hout := singular_escape d hmany (h1327 T L (standing d hc))
  have he : centralizer (V₁ : Set G) = Gv (markedZ d.flag.flag.module) := by
    conv_lhs => rw [←d.flag.flag.line_eq]
    rw [zpowers_eq_closure,centralizer_closure]
    rfl
  simpa only [he] using hout

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
