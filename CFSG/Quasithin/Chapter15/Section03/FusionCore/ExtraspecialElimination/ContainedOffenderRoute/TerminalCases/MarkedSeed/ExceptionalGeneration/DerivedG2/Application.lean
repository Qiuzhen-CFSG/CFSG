module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.MarkedSeed.ExceptionalGeneration.DerivedG2
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.MarkedSeed

/-!
# Derived G₂ generation applied to the original terminal seed

The proved unrestricted intrinsic theta-generation transports through
an actual equivalence from `starImage H L` to the commutator subgroup of the
split-octonion model. The original `r`, sections, orbits, B.2.14 and 15.3.48
inputs are retained; the seed point is constructed by the existing source
consumer. The model generation premise is fully discharged in
`exists_terminalPoint_of_g2_derived`; the earlier conditional reduction
remains available separately.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.49,
printed pp.1144–1145.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.MarkedSeed.ExceptionalGeneration
open Subgroup Representation Representation.BinaryOffender ModelExclusions
open ReducedModels ComponentReduction ModelReduction BinaryModels
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open Atlas.G2.BinaryParabolicPair

universe u
variable {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E L upper : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]

/-- Apply the proved reduction on the literal component quotient and original seed.
This conditional interface retains the independent seven-overgroup premise. -/
theorem exists_terminalPoint_of_g2_derived_of_seven_overgroups
    (r : ReducedModels.Input κ H M Y V Y0 T ZS Z E L upper)
    (sections : EarlierComponentSections κ)
    (orbits : OrbitClosure.EarlierOrbitAlternative κ)
    (hB214 : CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry.SourceB214Splitting.{u})
    (hZST : ZS ≤ T) (h48 : ⁅ZS, T⁆ ≤ Z) (hi : Z.relIndex ZS = 2)
    (e : starImage H L ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (seven : ∀ K : Subgroup DerivedModel,
      (derivedSylow : Subgroup DerivedModel) ≤ K → 7 ∣ Nat.card K → K = ⊤) :
    Nonempty (TerminalPoint r) := by
  exact exists_terminalPoint_of_component_generation r sections orbits hB214 hZST h48 hi
    ((g2_derived_of_seven_overgroups seven).of_mulEquiv e)

/-- The proved derived G₂ branch marks the original quotient seed, retaining
all earlier-source inputs and the actual component equivalence. -/
theorem exists_terminalPoint_of_g2_derived
    (r : ReducedModels.Input κ H M Y V Y0 T ZS Z E L upper)
    (sections : EarlierComponentSections κ)
    (orbits : OrbitClosure.EarlierOrbitAlternative κ)
    (hB214 : CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry.SourceB214Splitting.{u})
    (hZST : ZS ≤ T) (h48 : ⁅ZS, T⁆ ≤ Z) (hi : Z.relIndex ZS = 2)
    (e : starImage H L ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    Nonempty (TerminalPoint r) := by
  exact exists_terminalPoint_of_component_generation r sections orbits hB214 hZST h48 hi
    (g2_derived.of_mulEquiv e)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.MarkedSeed.ExceptionalGeneration
