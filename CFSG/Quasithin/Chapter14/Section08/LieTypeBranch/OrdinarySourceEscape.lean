module
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinarySourceChoice
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Escape

/-!
# The original point normalizer is an escaping local subgroup

The maximal ordinary A₆ source choice already supplies all of Hypothesis
12.2.3. Apply the original 12.2.13 escape theorem to its unchanged Irr⁺
module; natural A₆ transitivity moves the escaping vector to the original
line. Its order-two line then puts G₁ in the exact Hz family.

This removes the independent Hypothesis1223 and Hz-membership premises from
the ordinary source entry. The earlier universal 12.2.13 theorem remains
explicit and must be supplied by its source owner.
Source: Aschbacher--Smith13.3.6 and the opening of13.7--13.8,
printed pp.886,935,946, using12.2.13.
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

theorem original_six_point_normalizer_mem_Hz
    (hmax : Maximal (Counterexample T) L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (earlier : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u}) :
    G₁ ∈ Chapter13.Section08.Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M :=
  d.first_mem_Hz (hypothesis1223_of_maximal_six hmax e) earlier

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
