module
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinarySourceEscape
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.EscapeAt
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinarySourceChoice
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Escape

/-!
# The maximal ordinary point normalizer escapes using local recognition

The actual maximal ordinary A₆ counterexample supplies Hypothesis 12.2.3
before any escape conclusion. Apply ambient-local 12.2.13 to its unchanged
chosen natural module, transport its vector centralizer to the flag line,
and obtain G₁ itself in the original Hz family.
Source: Aschbacher–Smith 13.3.6 and the opening of 13.7–13.8, pp.886,935,946.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
open Chapter13.Section08.SourceCompletion Chapter13.Section07
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem original_six_point_normalizer_mem_Hz_at
    (hmax : Maximal (Counterexample T) L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (earlier : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T) :
    G₁ ∈ Chapter13.Section08.Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M :=
  d.first_mem_Hz_at (hypothesis1223_of_maximal_six hmax e) earlier

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
