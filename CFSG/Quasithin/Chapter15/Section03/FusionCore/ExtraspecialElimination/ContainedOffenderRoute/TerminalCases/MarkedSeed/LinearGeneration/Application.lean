module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.MarkedSeed.LinearGeneration
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.MarkedSeed

/-!
# Binary linear generation applied to the literal terminal seed

The intrinsic PSL₃(2), PSL₄(2), and PSL₅(2) generation theorems discharge the
linear premise of `generation_of_models`. For a supplied actual isomorphism
from L* to one of these projective groups, they also discharge the component
generation premise in the terminal-point construction. The latter retains
the original reduced input, its quotient seed, component sections, orbit
alternative, B.2.14, Z_S ≤ T, [Z_S,T] ≤ Z, and [Z_S:Z] = 2.

This is the linear model branch of the seed marking on Aschbacher–Smith,
combined manuscript (1 March 2004), printed pp.1144–1145. The independent
nonlinear model theorems and earlier-source producers remain with the
all-model source assembly; they are not inferred from a family tag.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases
open Subgroup Representation Representation.BinaryOffender ModelExclusions
open ReducedModels ComponentReduction ModelReduction BinaryModels MarkedSeed
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

namespace MarkedSeed.LinearGeneration

/-- Discharge precisely the linear branch in the existing all-model adapter. -/
theorem generation_of_models_of_nonlinear {D : Type*} [Group D] [Finite D]
    (hmodel : BinaryComponentModel D)
    (six : SylowThetaGeneration (alternatingGroup (Fin 6)))
    (seven : SylowThetaGeneration (alternatingGroup (Fin 7)))
    (cover : SylowThetaGeneration Atlas.Codes.HexEvenAutomorphisms)
    (g2 : SylowThetaGeneration (commutator (Atlas.G2.Model (ZMod 2)))) :
    SylowThetaGeneration D :=
  MarkedSeed.generation_of_models hmodel binary_linear six seven cover g2

end MarkedSeed.LinearGeneration

universe u
variable {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E L upper : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]

/-- The original seed gives a terminal point for any of the three actual
binary linear components. No point-stabilizer containment is assumed. -/
theorem exists_terminalPoint_of_linear_generation
    (r : ReducedModels.Input κ H M Y V Y0 T ZS Z E L upper)
    (sections : EarlierComponentSections κ)
    (orbits : OrbitClosure.EarlierOrbitAlternative κ)
    (hB214 : CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry.SourceB214Splitting.{u})
    (hZST : ZS ≤ T) (h48 : ⁅ZS, T⁆ ≤ Z) (hi : Z.relIndex ZS = 2)
    (n : ℕ) (lo : 3 ≤ n) (hiN : n ≤ 5)
    (e : starImage H L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) :
    Nonempty (TerminalPoint r) :=
  exists_terminalPoint_of_component_generation r sections orbits hB214 hZST h48 hi
    ((MarkedSeed.LinearGeneration.binary_linear n lo hiN).of_mulEquiv e)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases
