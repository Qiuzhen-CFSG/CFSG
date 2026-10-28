module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.RankOne
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.Source

/-!
# The rank-one exit feeds the original Chapter 13 setup

The source 6.2.20 one-or-two natural-module exit gives one natural copy on
any chosen Irr⁺ module. The same exit now supplies both the exact alternating
row of 12.2.2 and the original A₅ flag Context of 13.3.2. All subgroups lie
in the original ambient group; no replacement module is introduced.

Source: Aschbacher--Smith 12.2.2(3d) and 13.3.2(3), pp.795 and 885.
The earlier rank-one exit remains an explicit source input.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The rank-one producer simultaneously supplies the seven-case branch
and the actual flag Context required by the Chapter 13 consumer. -/
theorem alternatives_and_a5_context
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (hm : Chapter6.Source.IsOneOrTwoA5Modules L V) :
    ModuleAlternatives1222 D ∧
      ∃ V₁ V₂ V₃ : Subgroup G, V₂ ≤ V₃ ∧
        Nonempty (Chapter13.Section05.A5Source.Context T L V V₁ V₂ V₃) :=
  ⟨(D.alternatives_and_dimension_of_one_or_two_a5 hm).1,
    Chapter13.Section03.A5Setup.exists_context_of_one_or_two_modules h D hm⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
