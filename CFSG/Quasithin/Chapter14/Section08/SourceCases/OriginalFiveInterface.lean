module

public import CFSG.Quasithin.Chapter14.Section08.SourceCases
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Source523
import CFSG.Quasithin.Chapter14.Section08.SourceApplications.FiveOriginalModuleRows

/-!
# The original A5 branch behind a narrow source boundary

The actual guarded Chapter12 module rows and earlier 5.2.3 theorem supply
the original local arguments and the full model conclusion. The complete
source implementation is private to this interface.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section08.SourceCases.At.Interface
open Chapter12.Section02
open Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original A5 source uses the module theorem at every actual selected
Sylow and retains the genuine earlier 5.2.3 theorem. -/
theorem five_recognition
    (modules : ∀ S : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard →
        Theorem1222ModulesAt KnownSimple.IsKnownSimple S)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple) :
    FiveRecognition G :=
  fiveRecognition_from_original_module_rows modules h523

end CFSG.Quasithin.Chapter14.Section08.SourceCases.At.Interface
