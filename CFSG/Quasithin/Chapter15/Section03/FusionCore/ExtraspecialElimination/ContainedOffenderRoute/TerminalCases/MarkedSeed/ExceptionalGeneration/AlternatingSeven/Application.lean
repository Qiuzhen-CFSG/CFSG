module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.MarkedSeed.ExceptionalGeneration.AlternatingSeven
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.MarkedSeed

/-!
# Applying A₇ generation to the original terminal seed

The unrestricted Sylow-overgroup theorem for the actual alternating group
supplies the intrinsic generation premise through the given component
isomorphism. The seed construction retains the original reduced input,
earlier section and orbit hypotheses, B.2.14, and all three seed relations.
It constructs the terminal point without an assumed marking or stabilizer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the quotient
seed and point stabilizers in 15.3.49, printed pp.1144–1145.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.MarkedSeed.ExceptionalGeneration
open Subgroup Representation Representation.BinaryOffender ModelExclusions
open ReducedModels ComponentReduction ModelReduction BinaryModels
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

universe u
variable {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E L upper : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]

/-- The proved alternating seven branch marks the original quotient seed. -/
theorem exists_terminalPoint_of_alternating_seven
    (r : ReducedModels.Input κ H M Y V Y0 T ZS Z E L upper)
    (sections : EarlierComponentSections κ)
    (orbits : OrbitClosure.EarlierOrbitAlternative κ)
    (hB214 : CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry.SourceB214Splitting.{u})
    (hZST : ZS ≤ T) (h48 : ⁅ZS, T⁆ ≤ Z) (hi : Z.relIndex ZS = 2)
    (e : starImage H L ≃* alternatingGroup (Fin 7)) : Nonempty (TerminalPoint r) := by
  exact exists_terminalPoint_of_component_generation r sections orbits hB214 hZST h48 hi
    (alternating_seven.of_mulEquiv e)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.MarkedSeed.ExceptionalGeneration
