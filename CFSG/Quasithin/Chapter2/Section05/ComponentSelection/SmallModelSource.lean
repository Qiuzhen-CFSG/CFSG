module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallModelFacts
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ComponentSylowMark

/-!
# Actual component Sylow application of the small model facts

The subgroup is the original S ∩ L, formed using the actual ambient
inclusions. Subnormal Sylow intersection identifies it with a Sylow subgroup
of L. Thus the surviving model witness discharges assertions (1) and (3)
of Aschbacher--Smith 2.5.8, printed p.556, on the original source setup.
The witness is precisely the preceding 2.5.2/2.5.7 classification conclusion;
no outer-group or Sylow-shape premise is added.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup ComponentRefinement Stellmacher
variable {G : Type*} [Group G] [Finite G]
  {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- Assertions (1),(3) for the original component and its actual S-intersection. -/
theorem MathieuSourceSetup.small_model_outer_and_sylow
    (c : MathieuSourceSetup H L M S z) (hmodel : IsSmallRemainingComponent L) :
    IsPGroup 2 (MulAut.Outer L) ∧
      SourceSylowTwoShape (((S : Subgroup H).map H.subtype).subgroupOf L) := by
  obtain ⟨P, hP⟩ := MathieuSourceSetup.exists_relative_component_sylow c
  refine ⟨hmodel.outer_isTwoGroup, ?_⟩
  exact (hmodel.sylowTwoShape P).of_mulEquiv (MulEquiv.subgroupCongr hP.symm)

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
