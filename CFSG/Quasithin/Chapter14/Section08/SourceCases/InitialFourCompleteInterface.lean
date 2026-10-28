module
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section09.SourceSetup
import CFSG.Quasithin.Chapter12.Section06.NaturalSource.OriginalDegreeFourAt

/-! The original initial degree-four natural marking at the same Sylow. -/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section08.SourceCases.At.Interface
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G}

/-- Structural and module sources at the original Sylow give its literal
natural degree-four module, including the original action and projection. -/
theorem initial_four_natural
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hp : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 4 2)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    Chapter12.Section09.NaturalModule D 4 :=
  Chapter12.Section06.original_degree_four_natural_at h D hp structural modules hmany

end CFSG.Quasithin.Chapter14.Section08.SourceCases.At.Interface
