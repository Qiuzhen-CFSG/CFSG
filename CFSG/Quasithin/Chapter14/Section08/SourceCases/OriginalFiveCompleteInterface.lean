module
public import CFSG.Quasithin.Chapter14.Section08.SourceCases
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
import CFSG.Quasithin.Chapter14.Section08.SourceApplications.FiveOriginalModuleRowsWithout523

/-! Full original A₅ recognition from the guarded module family. -/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section08.SourceCases.At.Interface
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]

/-- The actual Chapter12 module family supplies the complete A₅ branch. -/
theorem five_recognition_complete
    (modules : ∀ S : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard →
        Theorem1222ModulesAt KnownSimple.IsKnownSimple S) : FiveRecognition G :=
  fiveRecognition_from_original_module_rows_without_source523 modules

end CFSG.Quasithin.Chapter14.Section08.SourceCases.At.Interface
