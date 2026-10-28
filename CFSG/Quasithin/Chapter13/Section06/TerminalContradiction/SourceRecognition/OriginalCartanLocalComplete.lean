module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.OriginalCartanLocalReduction
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.OriginalBinaryTrialityExclusion
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.Source523Application
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartan

/-!
# Local Cartan control in the original A₅ context

The original Cartan escape reduction has two outputs.  Its exceptional output
is the literal earlier-source alternative, which is contradictory in the
terminal context.  Its other output is an actual normal binary-triality
component of the singular centralizer, excluded by the original quadratic
actor construction.  Thus the same original hypotheses prove the local
normalization condition needed by the global Cartan step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open Components Components.SuzukiIsolation
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H A B : Subgroup G}

/-- Every compatible Cartan pair in the original terminal context has local
control.  The proof retains the actual `H`, `T`, and marked module throughout.
-/
theorem original_cartan_local_control
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) :
    CartanLocalControl A H := by
  by_contra hcontrol
  obtain ⟨Y, hY, hescape⟩ := exists_local_cartan_escape hcontrol
  obtain hl | ⟨X, hRX, hXC, hXL, hX, hXn, hm⟩ :=
    original_local_cartan_exceptional_or_binary_point_component
      d hmany hH hgen c hY hescape
  · exact terminal_contradiction_of_local_source523
      d hCv houtside hcounter hH hgen hl
  · exact original_normal_binary_triality_point_component_false
      d hCv houtside hcounter X (by
        have hV₁ : V₁ ≤ omegaOneCenterAmbient (T : Subgroup G) := by
          rw [← d.flag.flag.line_eq]
          exact zpowers_le.mpr d.flag.flag.z_central
        exact hXC.trans (centralizer_le hV₁)) hX hXn hm

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
