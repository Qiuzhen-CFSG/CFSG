module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OriginalOrdinaryCompletion
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryBlocksAt

/-!
# The original ordinary natural-six source from its genuine earlier inputs

The original local module theorems construct plane movement, point-normalizer
escape, the abelian full span and every F.9 application on the same natural
module and invariant flag. The completed component argument then excludes
all ordinary source rows. No plane, abelian-span, component, section, chief
factor, marked terminal model or universal local-input premise remains.

The chosen natural module and preceding Chapter12/13.3 results remain
explicit. The original central-quotient module construction and fixed-core
recognition provide their separate entry; the covered source is not asserted.
Source: Aschbacher--Smith 13.3.14,13.7.8,13.8.1--34,
printed pp.891--893,940--969.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open TransvectionRecognition.Component.ModelExtension
open Chapter14.Section08.LieTypeBranch

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}

/-- Exclude the unchanged original ordinary natural-six source from the
actual earlier local recognition and module inputs. -/
theorem original_ordinary_source_false_at
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (escape : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L) : False := by
  have hm := Section03.Noncentrality.ordinary_plane_noncentral_of_original_source_at
    d hmax eL escape h1332 fixed five
  obtain ⟨hHz,hspan,inputs⟩ :=
    Section03.Noncentrality.ordinary_selected_source_inputs_of_original_source_at
      d hmax eL escape h1332 fixed five
  exact original_ordinary_false_of_plane_noncentral (d.toLocalSetup hspan) eL
    (hypothesis1221_of_maximal_natural_six d hmax eL)
    (fun H hH => (inputs H hH).1) hm hHz

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
